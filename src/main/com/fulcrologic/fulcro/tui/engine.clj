(ns com.fulcrologic.fulcro.tui.engine
  "The pure TUI engine: the layout, paint, diff, focus, input, and overlay-compositing pipeline that
   turns a tree of terminal-native *nodes* into a character cell buffer (and ANSI), plus the
   component-render walker. This namespace also owns the node-structure vocabulary (the `::tag`/
   `::attrs`/`::children` keys and related specs) and the focus/scroll/caret state keys.

   Build the node tree with the element generators in `com.fulcrologic.fulcro.tui.elements`; drive it
   to a terminal with `com.fulcrologic.fulcro.tui.application`; paint to a concrete terminal via
   `com.fulcrologic.fulcro.tui.terminal`.

   A node is a plain map of the form:

   ```
   {:com.fulcrologic.fulcro.tui.engine/tag      :vbox        ; one of `tags`
    :com.fulcrologic.fulcro.tui.engine/attrs    {...}        ; layout/style/event attributes
    :com.fulcrologic.fulcro.tui.engine/children [...]}       ; child nodes, strings, and numbers
   ```

   This is JVM/babashka only (plain `.clj`)."
  (:require
    [clojure.spec.alpha :as s]
    [clojure.string :as str]
    [com.fulcrologic.fulcro.algorithms.denormalize :as fdn]
    [com.fulcrologic.fulcro.components :as comp]
    [com.fulcrologic.fulcro.raw.application :as rapp]
    [com.fulcrologic.fulcro.raw.components :as rc]
    [com.fulcrologic.fulcro.react.hooks :as hooks]
    [com.fulcrologic.fulcro.react.hooks-context :as hooks-ctx]
    [com.fulcrologic.fulcro.tui.perf :as perf :refer [p]]
    [com.fulcrologic.guardrails.core :refer [=> >def >defn >defn- ?]]))

;; ============================================================================
;; Node model + element generators
;; ============================================================================

(>def ::tag keyword?)
(>def ::attrs map?)
;; A child may also be an (as-yet unrendered) component instance produced by a
;; `comp/factory`; the walker (`render-tree`) replaces such instances with their rendered
;; node trees. We permit it here so element generators can splice component instances
;; into their children during a component's render.
(>def ::child (s/or :node ::node :text string? :number number?
                :component rc/component-instance?))
(>def ::children (s/coll-of ::child :kind vector?))
(>def ::node (s/keys :req [::tag ::attrs ::children]))

(>defn node?
  "Returns true if `x` is a TUI node: a map carrying a legal `::tag`."
  [x]
  [any? => boolean?]
  (some? (::tag x)))

;; ============================================================================
;; Character width (wcwidth-lite)
;; ============================================================================

(defn- in-range?
  "Returns true if the integer `cp` falls within any inclusive `[lo hi]` pair in `ranges`."
  [cp ranges]
  (boolean (some (fn [[lo hi]] (and (>= cp lo) (<= cp hi))) ranges)))

(def ^:private zero-width-ranges
  "Code point ranges (inclusive) that occupy zero terminal columns: combining marks, zero-width
   spaces/joiners, and variation selectors."
  [[0x0300 0x036F] [0x0483 0x0489] [0x0591 0x05BD] [0x200B 0x200F] [0x20D0 0x20FF] [0xFE00 0xFE0F]])

(def ^:private wide-ranges
  "Code point ranges (inclusive) that occupy two terminal columns: East Asian wide/fullwidth
   characters and common emoji/pictographs."
  [[0x1100 0x115F] [0x2329 0x232A] [0x2E80 0x303E] [0x3041 0x33FF] [0x3400 0x4DBF]
   [0x4E00 0x9FFF] [0xA000 0xA4CF] [0xAC00 0xD7A3] [0xF900 0xFAFF] [0xFE10 0xFE19]
   [0xFE30 0xFE6F] [0xFF00 0xFF60] [0xFFE0 0xFFE6] [0x1F300 0x1FAFF] [0x1F900 0x1F9FF]
   [0x20000 0x3FFFD]])

(>defn code-point-width
  "Returns the terminal column width (0, 1, or 2) of Unicode code point `cp`, using a compact
approximation of POSIX `wcwidth`: 0 for NUL, control characters, and combining/zero-width marks;
2 for East Asian wide/fullwidth characters and common emoji; 1 otherwise."
  [cp]
  [int? => int?]
  (cond
    (< cp 0x20) 0
    (and (>= cp 0x7F) (< cp 0xA0)) 0
    (in-range? cp zero-width-ranges) 0
    (in-range? cp wide-ranges) 2
    :else 1))

(defn- code-points
  "Returns a seq of the integer Unicode code points of string `s`."
  [^String s]
  (iterator-seq (.iterator (.codePoints s))))

(>defn string-width
  "Returns the total terminal column width of string `s` (the sum of its per-code-point widths).
Control characters, including newlines, contribute 0; callers that care about multi-line text
should split on newlines and measure each line."
  [s]
  [string? => int?]
  (reduce (fn [acc cp] (+ acc (code-point-width cp))) 0 (code-points s)))

(>defn- hard-break
  "Returns a vector of pieces of string `s`, each at most `width` display columns wide, splitting `s`
greedily at code-point boundaries (measured with `code-point-width`). Used to break an over-long
word that cannot fit on a single wrapped line. A piece never exceeds `width` columns, so a wide
(2-column) character is never split. Returns `[]` for the empty string."
  [s width]
  [string? int? => (s/coll-of string? :kind vector?)]
  (loop [cps (code-points s), cur (StringBuilder.), curw 0, out []]
    (if (seq cps)
      (let [cp (first cps)
            w  (code-point-width cp)]
        (if (and (pos? curw) (> (+ curw w) width))
          (recur cps (StringBuilder.) 0 (conj out (.toString cur)))
          (do (.appendCodePoint cur (int cp))
              (recur (rest cps) cur (+ curw w) out))))
      (if (pos? (.length cur)) (conj out (.toString cur)) out))))

(>defn- wrap-segment
  "Returns a vector of visual lines for a single newline-free `segment` greedily word-wrapped to
`width` display columns (words split on a single space, widths measured with `string-width`).
Words are packed onto a line separated by single spaces while they fit; a word that does not fit
starts a new line; a word wider than `width` is hard-broken (`hard-break`). When `width` is 0 or
negative the whole segment is returned as one line. An empty/blank segment yields a single empty
line."
  [segment width]
  [string? int? => (s/coll-of string? :kind vector?)]
  (if (<= width 0)
    [segment]
    (loop [words (str/split segment #" " -1), line "", linew 0, out []]
      (if (seq words)
        (let [word (first words)
              ww   (string-width word)]
          (cond
            (and (pos? linew) (<= (+ linew 1 ww) width))
            (recur (rest words) (str line " " word) (+ linew 1 ww) out)

            (<= ww width)
            (if (zero? linew)
              (recur (rest words) word ww out)
              (recur words "" 0 (conj out line)))

            :else
            (let [out    (if (pos? linew) (conj out line) out)
                  pieces (hard-break word width)]
              (recur (rest words) (last pieces) (string-width (last pieces))
                (into out (butlast pieces))))))
        (conj out line)))))

(def ^:private wrap-text-impl
  "Memoized worker for `wrap-text`. Word-wraps string `s` to `width` columns.

Memoized by `[s width]` value with a 5s TTL: wrapping is pure and is performed both during the
measure pass (`wrapped-line-count`) and the paint pass, so the same (string, width) is wrapped more
than once per frame. The TTL bounds memory as displayed text changes; `perf/cache` keeps it
babashka-safe."
  (perf/cache {:ttl-ms 5000 :gc-every 1000}
    (fn [s width]
      (into [] (mapcat #(wrap-segment % width)) (str/split (str s) #"\n" -1)))))

(>defn wrap-text
  "Returns a vector of visual-line strings produced by word-wrapping string `s` to `width` display
columns. `s` is first split on hard newlines (`\\n`), then each segment is greedily word-wrapped
(`wrap-segment`): words are packed left-to-right separated by single spaces while they fit on the
current line; a word that does not fit moves to the next line; a word wider than `width` is broken
hard at `width` columns (so a single over-long token never overflows). All widths are measured
with `string-width`/`code-point-width`, never `count`, so wide and zero-width characters are
handled correctly.

Conventions:
* An empty or all-spaces segment yields a single empty line (so a blank line in `s` is preserved
  as an empty visual line).
* `width <= 0` disables wrapping: each newline-separated segment becomes exactly one line.
* Leading/trailing spaces and runs of spaces inside a line may collapse when wrapping forces a
  break, but spaces are otherwise preserved within a line."
  [s width]
  [string? int? => (s/coll-of string? :kind vector?)]
  (p `wrap-text (wrap-text-impl s width)))

;; ============================================================================
;; Layout — measure pass (intrinsic sizes)
;; ============================================================================

(>def ::w nat-int?)
(>def ::h nat-int?)
(>def ::size (s/keys :req-un [::w ::h]))

(>defn edge-insets
  "Returns `{:l :r :t :b}` per-edge insets implied by `attrs`. `:border?` adds 1 to every edge and
`:padding` (a non-negative integer) adds its value to every edge."
  [attrs]
  [::attrs => map?]
  (let [e (+ (long (or (:padding attrs) 0)) (if (:border? attrs) 1 0))]
    {:l e :r e :t e :b e}))

(>defn- text-content
  "Returns the string formed by concatenating the string/number children of `node` (its text/label)."
  [node]
  [::node => string?]
  (apply str (map str (::children node))))

(>defn wrapping-text?
  "Returns true if `node` is a `:text` node whose attrs request line wrapping (`:wrap true`). Such a
text is laid out *height-for-width*: at place time its height is the number of visual lines its
content wraps to at its assigned width."
  [node]
  [any? => boolean?]
  (boolean (and (node? node) (= :text (::tag node)) (:wrap (::attrs node)))))

(>defn- wrapped-line-count
  "Returns the number of visual lines that wrapping-`text` `node` occupies when laid out into a
content width of `width` columns (the width inside any of the node's own insets). Always at least
one line."
  [node width]
  [::node int? => nat-int?]
  (max 1 (count (wrap-text (text-content node) width))))

(declare intrinsic-size)

(>defn- child-size
  "Returns the intrinsic `{:w :h}` of a child `c`, which may be a node, string, or number."
  [c]
  [any? => ::size]
  (cond
    (node? c) (intrinsic-size c)
    (string? c) {:w (string-width c) :h 1}
    (number? c) {:w (string-width (str c)) :h 1}
    :else {:w 0 :h 0}))

(>defn- internal-content-size
  "Returns the content-driven intrinsic `{:w :h}` of a BUILT-IN `node` for its tag, before the node's
own fixed `:width`/`:height` or `:min-*` overrides are applied. Container sizes include edge insets.
The `case` default is a terminal fallback (insets only) used for an unregistered custom tag — a custom
tag that declares `:width`/`:height` still sizes via the overrides applied in `intrinsic-size-impl`."
  [node]
  [::node => ::size]
  (let [{::keys [tag attrs]} node
        {:keys [l r t b]} (edge-insets attrs)
        iw (+ l r)
        ih (+ t b)]
    (case tag
      :text (let [lines (str/split (text-content node) #"\n" -1)]
              {:w (+ iw (apply max 0 (map string-width lines)))
               :h (+ ih (max 1 (count lines)))})
      :button {:w (+ iw (string-width (text-content node))) :h (+ ih 1)}
      :input {:w (+ iw (max 1 (string-width (str (:value attrs "")))))
              :h (+ ih (if (:multiline? attrs) 3 1))}
      :line {:w 1 :h 1}
      :viewport {:w (if (number? (:width attrs)) (:width attrs) 0)
                 :h (if (number? (:height attrs)) (:height attrs) 0)}
      (:vbox :box :modal) (let [sizes (map child-size (::children node))]
                            {:w (+ iw (apply max 0 (map :w sizes)))
                             :h (+ ih (reduce + 0 (map :h sizes)))})
      :hbox (let [sizes (map child-size (::children node))]
              {:w (+ iw (reduce + 0 (map :w sizes)))
               :h (+ ih (apply max 0 (map :h sizes)))})
      {:w iw :h ih})))

(defmulti content-size
  "Returns the content-driven intrinsic `{:w :h}` of `node` for its `::tag`, BEFORE the node's own
`:width`/`:height`/`:min-*` overrides (which `intrinsic-size` applies). Extension seam for custom
RENDERED tags: register the natural size of your tag with `(defmethod content-size :my/tag [node]
{:w .. :h ..})` (include any `:padding`/`:border?` insets yourself — see `edge-insets`). Built-in
tags are handled by `:default`; an unregistered custom tag falls back to insets-only."
  (fn [node] (::tag node)))

(defmethod content-size :default [node] (internal-content-size node))

(def ^:private intrinsic-size-impl
  "Memoized worker for `intrinsic-size`. Computes the intrinsic size of an UNPLACED `node` from its
content size and own `:width`/`:height`/`:min-*` overrides.

Memoized by node VALUE with a 5s TTL: `intrinsic-size` is pure on its (unplaced) node arg, and a
single render measures the same node instances repeatedly — directly (a parent's `distribute-main`
asks each child) and transitively (`content-size`→`child-size` recurses the whole subtree, and each
descendant container then re-measures its own subtree during `place`). Because `child-size` calls
the `intrinsic-size` var, every recursive level routes back through this cache, so a parent reuses
the sizes its descendants computed moments earlier (collapsing the O(n·depth) re-measure to O(n)).

The TTL bounds memory: entries for node maps that no longer appear (the UI changed) expire instead
of leaking. Caching forever would retain stale node values across every frame. `:gc-every 1000`
sweeps expired entries roughly once per 1000 calls. Built on `perf/cache` (atom + delay), so it is
babashka-safe (no arrays/interop)."
  (perf/cache {:ttl-ms 5000 :gc-every 1000}
    (fn [node]
      (let [{:keys [width height min-width min-height]} (::attrs node)
            {:keys [w h]} (content-size node)]
        {:w (max (if (number? width) width w) (long (or min-width 0)))
         :h (max (if (number? height) height h) (long (or min-height 0)))}))))

(>defn intrinsic-size
  "Returns the intrinsic `{:w :h}` of `node` in terminal cells. The content size (text length,
stacked/abutted children, plus any `:border?`/`:padding` insets) is overridden by the node's own
fixed `:width`/`:height` when those are integers, and then floored by `:min-width`/`:min-height`.
Fraction and `:grow` sizing are not resolved here — they require a concrete parent rectangle and
are handled by the place pass.

The result is memoized by node value (see `intrinsic-size-impl`); this is the public, transparent
entry point and is what `child-size` recurses through, so every subtree level hits the cache."
  [node]
  [::node => ::size]
  (intrinsic-size-impl node))

;; ============================================================================
;; Layout — place pass (rect assignment)
;; ============================================================================

(>def ::x int?)
(>def ::y int?)
(>def ::rect (s/keys :req-un [::x ::y ::w ::h]))

(>defn as-node
  "Returns `c` unchanged if it is a node, otherwise wraps it as a `:text` node. Lets containers hold
bare strings/numbers, which become text lines."
  [c]
  [any? => ::node]
  ;; Build the text node inline (don't call the `elements` constructor) so the engine has no
  ;; dependency on `tui.elements` — the dependency runs one way: elements -> engine.
  (if (node? c) c {::tag :text ::attrs {} ::children [(str c)]}))

(>defn- resolve-size
  "Resolves a child size `spec` against the available main-axis `extent` and the child's `intrinsic`
size. A number is a fixed cell count; `:half` is half the extent; `[:fraction f]` is that fraction
of the extent (rounded); `nil` (or anything else) falls back to the intrinsic size."
  [spec extent intrinsic]
  [any? nat-int? nat-int? => nat-int?]
  (cond
    (number? spec) (long spec)
    (= :half spec) (quot extent 2)
    (and (vector? spec) (= :fraction (first spec)))
    (long (Math/round (* (double extent) (double (second spec)))))
    :else intrinsic))

(>defn- align-offset
  "Returns the offset of a child of `size` within a track of `extent` for the given `align` keyword.
`:center`/`:middle` center it, `:end`/`:right`/`:bottom` push it to the far edge, anything else
(default) keeps it at the near edge."
  [align extent size]
  [any? nat-int? nat-int? => int?]
  (case align
    (:center :middle) (quot (max 0 (- extent size)) 2)
    (:end :right :bottom) (max 0 (- extent size))
    0))

(>defn- main-content-size
  "Returns the content-driven main-axis size of child `c` being stacked along `main-attr`
(`:height` for a vbox, `:width` for an hbox) given the `cross-extent` (the cross-axis track size
the child will fill). For a wrapping `:text` stacked vertically this is its wrapped line count at
the available content width (`cross-extent` minus the node's own insets); otherwise it is the
child's ordinary intrinsic size on the main axis."
  [c cross-extent main-attr]
  [::node nat-int? keyword? => nat-int?]
  (if (and (= main-attr :height) (wrapping-text? c))
    (let [{:keys [l r]} (edge-insets (::attrs c))
          {:keys [t b]} (edge-insets (::attrs c))]
      (+ t b (wrapped-line-count c (max 0 (- cross-extent l r)))))
    (get (intrinsic-size c) (if (= main-attr :height) :h :w))))

(>defn- distribute-main
  "Returns a vector of resolved main-axis sizes (one per child) that partition `extent`. Children
with a `:grow` weight share the space left over after fixed/fraction/content-sized children;
leftover is split by weight with any rounding remainder given to the last grow child. `cross-extent`
is the cross-axis track size each child will fill, used to resolve height-for-width wrapping text."
  [extent cross-extent children main-attr]
  [nat-int? nat-int? (s/coll-of ::node) keyword? => (s/coll-of nat-int?)]
  (let [info       (mapv (fn [c]
                           (let [a    (::attrs c)
                                 intr (main-content-size c cross-extent main-attr)]
                             {:grow  (:grow a)
                              :fixed (when-not (:grow a)
                                       (resolve-size (get a main-attr) extent intr))}))
                     children)
        used       (reduce + 0 (keep :fixed info))
        leftover   (max 0 (- extent used))
        weights    (keep :grow info)
        total-w    (reduce + 0 weights)
        grow-sizes (if (pos? total-w)
                     (loop [acc [], rem leftover, ws weights]
                       (if (seq ws)
                         (let [w  (first ws)
                               sz (if (= 1 (count ws)) rem (quot (* leftover w) total-w))]
                           (recur (conj acc sz) (- rem sz) (rest ws)))
                         acc))
                     [])]
    (:out (reduce (fn [{:keys [out gs]} {:keys [grow fixed]}]
                    (if grow
                      {:out (conj out (first gs)) :gs (rest gs)}
                      {:out (conj out fixed) :gs gs}))
            {:out [] :gs grow-sizes}
            info))))

(>def ::scroll (s/keys :req-un [::x ::y]))
;; A placed multiline `:input` node carries `::text-scroll`, the internal top visual-line offset that
;; scrolls its wrapped value so the caret stays visible. The driver injects it during render.
(>def ::text-scroll (? nat-int?))

(>defn clamp-scroll
  "Returns the `scroll` offset `{:x :y}` clamped so the visible window stays within the virtual
content. Given the `virtual-size` `{:w :h}` of the laid-out child and the `view-size` `{:w :h}`
of the viewport's content area, each axis is clamped to `0..(max 0 (- virtual view))`. When the
virtual content is no larger than the view, that axis clamps to 0. Pure."
  [scroll virtual-size view-size]
  [::scroll ::size ::size => ::scroll]
  (let [max-x (max 0 (- (:w virtual-size) (:w view-size)))
        max-y (max 0 (- (:h virtual-size) (:h view-size)))]
    {:x (max 0 (min (long (:x scroll)) max-x))
     :y (max 0 (min (long (:y scroll)) max-y))}))

(defmulti place
  "Returns `node` laid out within the outer `rect` `{:x :y :w :h}`: annotates it with its `::rect` and
replaces `::children` with placed children (each carrying its own `::rect`). Dispatches on `::tag`.

Extension seam for custom RENDERED tags: register a custom CONTAINER's layout with `(defmethod place
:my/tag [node rect] ...)`. To lay children out like a `:vbox`/`:hbox`, reuse `place-stack`; to place a
single child, call `place` recursively; use `edge-insets`/`as-node` for the content rect and child
coercion. Built-in tags are handled by `:default`; an unregistered custom tag is treated as a leaf
(gets a `::rect`, children left for its paint method)."
  (fn [node _rect] (::tag node)))

(>defn place-stack
  "Places `children` within the `content` rectangle along `axis` (`:v` stacks vertically, `:h`
horizontally). Main-axis sizes are distributed by `distribute-main`; on the cross axis each child
fills the track unless it declares a size, in which case `:align` positions it. Returns the vector
of placed children. Public so a custom container's `place` method can reuse the built-in
`:vbox`/`:hbox` layout."
  [axis content children]
  [#{:v :h} ::rect (s/coll-of ::node) => vector?]
  (let [vertical?    (= axis :v)
        main-extent  (if vertical? (:h content) (:w content))
        cross-extent (if vertical? (:w content) (:h content))
        main-attr    (if vertical? :height :width)
        cross-attr   (if vertical? :width :height)
        main-sizes   (distribute-main main-extent cross-extent children main-attr)]
    (loop [offset 0, cs (seq children), ms (seq main-sizes), out []]
      (if cs
        (let [c          (first cs)
              msz        (first ms)
              a          (::attrs c)
              intr-cross (get (intrinsic-size c) (if vertical? :w :h))
              cross-spec (get a cross-attr)
              cross-size (if (some? cross-spec)
                           (min cross-extent (resolve-size cross-spec cross-extent intr-cross))
                           cross-extent)
              cross-off  (align-offset (:align a) cross-extent cross-size)
              rect       (if vertical?
                           {:x (+ (:x content) cross-off) :y (+ (:y content) offset) :w cross-size :h msz}
                           {:x (+ (:x content) offset) :y (+ (:y content) cross-off) :w msz :h cross-size})]
          (recur (+ offset msz) (next cs) (next ms) (conj out (place c rect))))
        out))))

(>defn- internal-place
  "Lays out a BUILT-IN `node` within the outer `rect` (the `place` `:default`). `:vbox`/`:hbox`
partition their content area among children (honoring fixed/`:half`/`:fraction`/`:grow`/content
sizing and `:align`); `:box` fills its content area with each child; leaves keep their string/number
children for the paint pass. `:border?`/`:padding` inset the content area.

A `:viewport` is special: it has a bounded outer `::rect` (sized like any box), but its single
child is laid out at the child's NATURAL height (and the viewport's content width) into a VIRTUAL
rect `{:x 0 :y 0 :w content-w :h (max content-h natural-h)}` — i.e. in 0-based virtual coordinates
rather than absolute screen coordinates. The placed virtual child subtree is stored under
`::viewport-content`, the virtual content size under `::virtual-size {:w :h}`, and a default
`::scroll {:x 0 :y 0}` is attached (the driver later injects the real scroll). The viewport's
`::children` are also placed (in virtual coords) so generic walkers still see them.

The `case` default is the terminal leaf placement (annotate `::rect`, keep children), used by the
built-in leaves AND by an unregistered custom tag — so it must NOT re-enter `place`."
  [node rect]
  [::node ::rect => (s/keys :req [::tag ::attrs ::rect ::children])]
  (let [{::keys [tag attrs children]} node
        {:keys [l r t b]} (edge-insets attrs)
        content {:x (+ (:x rect) l)
                 :y (+ (:y rect) t)
                 :w (max 0 (- (:w rect) l r))
                 :h (max 0 (- (:h rect) t b))}]
    (case tag
      (:vbox :modal) (assoc node ::rect rect ::children (place-stack :v content (mapv as-node children)))
      :hbox (assoc node ::rect rect ::children (place-stack :h content (mapv as-node children)))
      :viewport
      (let [child        (as-node (first children))
            ;; A wrapping text inside a viewport wraps to the viewport's content width, so its
            ;; natural (virtual) height is its wrapped line count at that width rather than 1.
            natural-h    (if (wrapping-text? child)
                           (wrapped-line-count child (:w content))
                           (:h (intrinsic-size child)))
            virtual-h    (max (:h content) natural-h)
            virtual      {:x 0 :y 0 :w (:w content) :h virtual-h}
            placed-child (place child virtual)]
        (assoc node
          ::rect rect
          ::children [placed-child]
          ::viewport-content placed-child
          ::virtual-size {:w (:w content) :h virtual-h}
          ::scroll {:x 0 :y 0}))
      :box (assoc node ::rect rect ::children (mapv #(place (as-node %) content) children))
      (assoc node ::rect rect ::children children))))

(defmethod place :default [node rect]
  (p ::place (internal-place node rect)))

;; ============================================================================
;; Render — cell buffer
;; ============================================================================

(>def ::palette-color
  #{:black :red :green :yellow :blue :magenta :cyan :white
    :bright-black :bright-red :bright-green :bright-yellow
    :bright-blue :bright-magenta :bright-cyan :bright-white})

(>def ::style
  (s/keys :opt-un [::fg ::bg ::bold? ::reverse? ::underline?]))
(>def ::fg ::palette-color)
(>def ::bg ::palette-color)
(>def ::bold? boolean?)
(>def ::reverse? boolean?)
(>def ::underline? boolean?)

(>def ::ch char?)
(>def ::sgr ::style)
(>def ::cell (s/keys :req-un [::ch ::sgr]))
(>def ::rows nat-int?)
(>def ::cols nat-int?)
(>def ::cells (s/coll-of ::cell :kind vector?))
(>def ::buffer (s/keys :req-un [::rows ::cols ::cells]))

(def ^:private blank-cell
  "The default cell: a space with the default (empty) style."
  {:ch \space :sgr {}})

(>defn make-buffer
  "Returns a blank cell buffer of `rows` by `cols`. Every cell is a space with the default (empty)
style. Cells are stored row-major in a flat vector of length `rows`*`cols`."
  [rows cols]
  [nat-int? nat-int? => ::buffer]
  {:rows rows :cols cols :cells (vec (repeat (* rows cols) blank-cell))})

(>defn- in-bounds?
  "Returns true if the 0-based column `x` and row `y` lie inside the `rows`x`cols` `buffer`."
  [buffer x y]
  [::buffer int? int? => boolean?]
  (and (>= x 0) (>= y 0) (< x (:cols buffer)) (< y (:rows buffer))))

(>defn put-cell
  "Returns `buffer` with the cell at 0-based column `x`, row `y` set to character `ch` with `style`.
Writes that fall outside the buffer bounds are ignored (clipped), returning the buffer unchanged."
  [buffer x y ch style]
  [::buffer int? int? char? ::style => ::buffer]
  (if (in-bounds? buffer x y)
    (assoc-in buffer [:cells (+ x (* y (:cols buffer)))] {:ch ch :sgr style})
    buffer))

(>defn in-clip?
  "Returns true if column `x`, row `y` is inside the `clip` rect `{:x :y :w :h}`."
  [clip x y]
  [::rect int? int? => boolean?]
  (and (>= x (:x clip)) (>= y (:y clip))
    (< x (+ (:x clip) (:w clip)))
    (< y (+ (:y clip) (:h clip)))))

(>defn- put-str*
  "Writes string `s` into `buffer` starting at `x`,`y`; implementation for `put-str`."
  [buffer x y s style clip-rect]
  [::buffer int? int? string? ::style ::rect => ::buffer]
  (loop [buf buffer
         col x
         cps (code-points s)]
    (if (seq cps)
      (let [cp (first cps)
            w  (code-point-width cp)]
        (cond
          (zero? w) (recur buf col (rest cps))
          (= 2 w) (let [c2 (inc col)]
                    (if (and (in-clip? clip-rect col y) (in-clip? clip-rect c2 y))
                      (recur (-> buf
                               (put-cell col y (char cp) style)
                               (put-cell c2 y \space style))
                        (+ col 2) (rest cps))
                      (recur buf (+ col 2) (rest cps))))
          :else (if (in-clip? clip-rect col y)
                  (recur (put-cell buf col y (char cp) style) (inc col) (rest cps))
                  (recur buf (inc col) (rest cps)))))
      buf)))

(>defn put-str
  "Returns `buffer` with string `s` written starting at 0-based column `x`, row `y`, advancing by each
character's display width and styling each written cell with `style`. Writes are clipped to both
the `clip-rect` `{:x :y :w :h}` and the buffer bounds.

Wide-char cell scheme: a 2-column character is written into its starting cell and a continuation
marker (a space with the same `style`) is written into the next cell. The `screen` helper drops
these continuation cells so screen strings read naturally. A wide char is written only if BOTH its
cells pass the clip/bounds test, so a wide char is never split across a clip boundary."
  [buffer x y s style clip-rect]
  [::buffer int? int? string? ::style ::rect => ::buffer]
  (p `put-str (put-str* buffer x y s style clip-rect)))

;; ============================================================================
;; Render — color palette + SGR
;; ============================================================================

(def palette
  "Map of palette color keywords to their foreground SGR base codes. Standard colors map to 30..37 and
   bright colors to 90..97. A background code is the foreground code plus 10."
  {:black        30 :red 31 :green 32 :yellow 33
   :blue         34 :magenta 35 :cyan 36 :white 37
   :bright-black 90 :bright-red 91 :bright-green 92 :bright-yellow 93
   :bright-blue  94 :bright-magenta 95 :bright-cyan 96 :bright-white 97})

(>defn style->sgr-codes
  "Returns the ordered vector of SGR integer codes for `style`. Attribute codes come first (reverse=7,
bold=1, underline=4), followed by the foreground color code and then the background color code
(foreground base + 10). The empty/default style yields an empty vector."
  [style]
  [::style => (s/coll-of nat-int? :kind vector?)]
  (cond-> []
    (:reverse? style) (conj 7)
    (:bold? style) (conj 1)
    (:underline? style) (conj 4)
    (:fg style) (conj (palette (:fg style)))
    (:bg style) (conj (+ 10 (palette (:bg style))))))

(>defn sgr-string
  "Returns the ANSI SGR escape string for the vector of integer `codes`, e.g. `[1 31]` becomes the CSI
select-graphic-rendition sequence `\"\\u001b[1;31m\"`. An empty `codes` vector yields the reset
sequence `\"\\u001b[0m\"`."
  [codes]
  [(s/coll-of nat-int? :kind vector?) => string?]
  (str "[" (str/join ";" (if (seq codes) codes [0])) "m"))

;; ============================================================================
;; Render — paint
;; ============================================================================

(>defn node-style
  "Returns the `::style` map implied by a node's `attrs`. `:highlight true` sets `:reverse?`,
`:color <kw>` sets `:fg`, `:bg <kw>` sets `:bg`, `:bold true` sets `:bold?`, and `:underline true`
sets `:underline?`."
  [attrs]
  [::attrs => ::style]
  (cond-> {}
    (:highlight attrs) (assoc :reverse? true)
    (:color attrs) (assoc :fg (:color attrs))
    (:bg attrs) (assoc :bg (:bg attrs))
    (:bold attrs) (assoc :bold? true)
    (:underline attrs) (assoc :underline? true)))

(>defn needs-bg-fill?
  "Returns true if a container styled with `style` must fill its area with spaces. Only a background
(`:bg`) or reverse-video (`:reverse?`) style changes how a *blank* cell looks; a foreground- or
bold-only style does not (a space paints no glyph, so its fg/bold is invisible). Skipping the fill
for fg/bold-only containers avoids an O(area) per-cell write — a large saving for big containers
(e.g. a `:grow` viewport or frame tinted with a `:color`)."
  [style]
  [::style => boolean?]
  (boolean (or (:bg style) (:reverse? style))))

(>defn rect-intersection
  "Returns the rectangle that is the intersection of rects `a` and `b`. When they do not overlap the
result has zero (or negative-clamped) width/height."
  [a b]
  [::rect ::rect => ::rect]
  (let [x  (max (:x a) (:x b))
        y  (max (:y a) (:y b))
        x2 (min (+ (:x a) (:w a)) (+ (:x b) (:w b)))
        y2 (min (+ (:y a) (:h a)) (+ (:y b) (:h b)))]
    {:x x :y y :w (max 0 (- x2 x)) :h (max 0 (- y2 y))}))

(>defn fill-rect
  "Returns `buffer` with every cell of `rect` set to a space in `style`, clipped to `clip`."
  [buffer rect style clip]
  [::buffer ::rect ::style ::rect => ::buffer]
  (reduce
    (fn [buf row]
      (reduce
        (fn [b col]
          (if (in-clip? clip col row)
            (put-cell b col row \space style)
            b))
        buf
        (range (:x rect) (+ (:x rect) (:w rect)))))
    buffer
    (range (:y rect) (+ (:y rect) (:h rect)))))

(>defn draw-border
  "Returns `buffer` with a single-cell box-drawing border (`┌┐└┘` corners, `─` top/bottom, `│` sides)
drawn around the outer `rect`, clipped to `clip`. Boxes smaller than 2x2 are not drawn."
  [buffer rect style clip]
  [::buffer ::rect ::style ::rect => ::buffer]
  (let [{:keys [x y w h]} rect
        x2 (+ x w -1)
        y2 (+ y h -1)]
    (if (and (>= w 2) (>= h 2))
      (let [put (fn [b cx cy ch] (if (in-clip? clip cx cy) (put-cell b cx cy ch style) b))]
        (as-> buffer $
          (reduce (fn [b cx] (-> b (put cx y \─) (put cx y2 \─))) $ (range (inc x) x2))
          (reduce (fn [b cy] (-> b (put x cy \│) (put x2 cy \│))) $ (range (inc y) y2))
          (put $ x y \┌)
          (put $ x2 y \┐)
          (put $ x y2 \└)
          (put $ x2 y2 \┘)))
      buffer)))

(>defn content-rect
  "Returns the inner content rectangle of placed `node`: its `::rect` shrunk by the edge insets implied
by its attrs (`:border?`/`:padding`)."
  [node]
  [::node => ::rect]
  (let [r (::rect node)
        {:keys [l r' t b]} (let [{:keys [l r t b]} (edge-insets (::attrs node))] {:l l :r' r :t t :b b})]
    {:x (+ (:x r) l)
     :y (+ (:y r) t)
     :w (max 0 (- (:w r) l r'))
     :h (max 0 (- (:h r) t b))}))

(>defn blit
  "Returns `dest` buffer with the `[src-x src-y w h]` window of the `src` buffer copied so that the
window's top-left lands at `dest-x`,`dest-y` in `dest`. Each copied cell is written via `put-cell`,
so writes are clipped to `dest`'s bounds; in addition, copies are clipped to `clip` (a dest-space
rect). Cells read from outside `src`'s bounds are skipped. Pure."
  [dest src src-x src-y w h dest-x dest-y clip]
  [::buffer ::buffer int? int? nat-int? nat-int? int? int? ::rect => ::buffer]
  (let [src-cols  (:cols src)
        src-rows  (:rows src)
        src-cells (:cells src)]
    (reduce
      (fn [b row]
        (reduce
          (fn [b col]
            (let [sx (+ src-x col)
                  sy (+ src-y row)
                  dx (+ dest-x col)
                  dy (+ dest-y row)]
              (if (and (>= sx 0) (>= sy 0) (< sx src-cols) (< sy src-rows)
                    (in-clip? clip dx dy))
                (let [{:keys [ch sgr]} (nth src-cells (+ sx (* sy src-cols)))]
                  (put-cell b dx dy ch sgr))
                b)))
          b
          (range 0 w)))
      dest
      (range 0 h))))

(>defn- translate-placed
  "Returns placed `node` with `(dx,dy)` added to its own `::rect` and recursively to every descendant's
— EXCEPT it does not descend into a nested `:viewport`'s virtual content (that subtree lives in the
nested viewport's own coordinate space and is repainted when that viewport paints; only the nested
viewport's outer rect shifts). Used to paint just a viewport's visible window: the content is shifted
by `-scroll` so the visible region lands at the window buffer's origin."
  [node dx dy]
  [any? int? int? => any?]
  (if (node? node)
    (let [r    (::rect node)
          node (if r (assoc node ::rect (-> r (update :x + dx) (update :y + dy))) node)]
      (if (= :viewport (::tag node))
        node
        (update node ::children
          (fn [cs] (mapv (fn [c] (if (node? c) (translate-placed c dx dy) c)) cs)))))
    node))

(defmulti paint
  "Returns `buffer` after painting placed `node` (and its descendants) into it, clipping all writes to
`clip`. Dispatches on `::tag`. Uses the painter's algorithm: a node paints itself (border/background
or its text) then its children, so children draw over parents.

Extension seam for custom RENDERED tags: register `(defmethod paint :my/tag [buffer node clip] ...)`,
drawing into `buffer` with the public painter toolkit (`put-cell`, `put-str`, `fill-rect`,
`draw-border`, `blit`, `node-style`, `content-rect`, `rect-intersection`, `in-clip?`); to paint
children, call `paint` recursively. Built-in tags are handled by `:default`; an unregistered custom
tag paints nothing."
  (fn [_buffer node _clip] (::tag node)))

(declare render-buffer)
(declare wrap-layout)
(declare multiline-input?)

(defn- paint-id
  "Returns the perf id for painting a node of `tag`, e.g. `:paint/text`."
  [tag]
  (keyword "paint" (name tag)))

(def ^:dynamic *enhanced-keys?*
  "True when the terminal's enhanced (Kitty/CSI-u) keyboard protocol is active, bound by the driver
   during a render. Gates mnemonic-underline rendering: shortcut hints are shown only when the
   shortcut can actually be captured. Defaults to `false`."
  false)

(>defn chord-base-key
  "Returns the base (non-modifier) key of a `key-chord`-form `shortcut`: the last element of a
modifier vector (e.g. `\"s\"` for `[:alt \"s\"]`), or the chord itself when it is a bare key."
  [shortcut]
  [any? => any?]
  (if (vector? shortcut) (peek shortcut) shortcut))

(>defn- shortcut-mnemonic
  "Returns the single mnemonic letter (lowercased) implied by a node's `:shortcut` attr — the chord's
base key when it is a single letter — or nil when there is none (e.g. a special-key chord like `:f2`,
or a non-letter)."
  [attrs]
  [::attrs => (? string?)]
  (let [base (chord-base-key (:shortcut attrs))]
    (when (and (string? base) (= 1 (count base)) (Character/isLetter (.charAt ^String base 0)))
      (str/lower-case base))))

(>defn- paint-mnemonic
  "Returns `buffer` with the first cell matching mnemonic letter `m` (case-insensitive) across `lines`
re-painted in `style` plus an underline attribute. `x`/`y` are the content-rect origin; the matching
column accounts for the display width of the preceding text. Writes are clipped to `clip`. When no
line contains `m`, the buffer is returned unchanged."
  [buffer lines x y m style clip]
  [::buffer (s/coll-of string?) int? int? string? ::style ::rect => ::buffer]
  (loop [i 0 ls lines]
    (if (seq ls)
      (let [line (first ls)
            idx  (str/index-of (str/lower-case line) m)]
        (if idx
          (let [col (+ x (string-width (subs line 0 idx)))]
            (put-str buffer col (+ y i) (subs line idx (inc idx)) (assoc style :underline? true) clip))
          (recur (inc i) (rest ls))))
      buffer)))

(>defn- internal-paint
  "Returns `buffer` after painting a BUILT-IN placed `node` and its descendants (the `paint`
`:default`), clipping every write to `clip` (the intersection of ancestor rects). Containers draw
their border/background then recurse (via `paint`, so custom children dispatch); leaves write their
text/value/rule into their content rect. The `case` default is a terminal fallback (paint nothing)
for an unregistered custom tag — it must NOT re-enter `paint`."
  [buffer node clip]
  [::buffer ::node ::rect => ::buffer]
  (let [{::keys [tag attrs children]} node
        rect         (::rect node)
        style        (node-style attrs)
        node-clip    (rect-intersection clip rect)
        cr           (content-rect node)
        content-clip (rect-intersection node-clip cr)]
    (if (or (<= (:w node-clip) 0) (<= (:h node-clip) 0))
      ;; Cull: the node's rect lies entirely outside the current clip, so neither it nor any of its
      ;; descendants can paint a visible cell — skip the whole subtree instead of walking it. This is
      ;; what lets a viewport painted into a window-sized buffer (see `:viewport`) avoid touching the
      ;; rows that are scrolled out of view.
      buffer
      (case tag
        (:text :button)
        (let [lines (if (wrapping-text? node)
                      (wrap-text (text-content node) (:w cr))
                      (str/split (text-content node) #"\n" -1))
              buf   (reduce
                      (fn [b [i line]]
                        (put-str b (:x cr) (+ (:y cr) i) line style content-clip))
                      buffer
                      (map-indexed vector lines))
              m     (when *enhanced-keys?* (shortcut-mnemonic attrs))]
          (if m
            (paint-mnemonic buf lines (:x cr) (:y cr) m style content-clip)
            buf))

        :input
        (if (multiline-input? node)
          ;; A multiline input renders its value wrapped to its content width, scrolled vertically by
          ;; the internal top-line offset (`::text-scroll`, injected by the driver to keep the caret
          ;; visible). Each visible visual row is painted into its rect row (clipped).
          (let [top    (max 0 (long (or (::text-scroll node) 0)))
                lines  (mapv :text (wrap-layout (str (:value attrs "")) (:w cr)))
                window (subvec lines (min top (count lines)) (min (+ top (:h cr)) (count lines)))]
            (reduce
              (fn [b [i line]]
                (put-str b (:x cr) (+ (:y cr) i) line style content-clip))
              buffer
              (map-indexed vector window)))
          (put-str buffer (:x cr) (:y cr) (str (:value attrs "")) style content-clip))

        :line
        (let [{:keys [x y w h]} rect
              horizontal? (>= w h)
              rule        (if horizontal? \─ \│)]
          (reduce
            (fn [b [cx cy]]
              (if (in-clip? node-clip cx cy) (put-cell b cx cy rule style) b))
            buffer
            (for [cy (range y (+ y h)) cx (range x (+ x w))] [cx cy])))

        :viewport
        ;; Render ONLY the visible window: shift the virtual child up/left by the scroll offset and
        ;; paint it into a buffer sized to the viewport's CONTENT rect (not the full virtual content),
        ;; then blit that window into the content rect in the main buffer. Rows/columns scrolled out of
        ;; view land at negative coords and are culled (their rect no longer intersects the window
        ;; buffer), so off-screen content is never painted — a large saving for a tall list. The
        ;; border (if any) is drawn on the outer rect.
        (let [vsize      (or (::virtual-size node) {:w 0 :h 0})
              vchild     (::viewport-content node)
              raw-scroll (or (::scroll node) {:x 0 :y 0})
              scroll     (clamp-scroll raw-scroll vsize {:w (:w cr) :h (:h cr)})
              buf        (if (needs-bg-fill? style) (fill-rect buffer cr style content-clip) buffer)
              buf        (if (:border? attrs) (draw-border buf rect style node-clip) buf)
              buf        (if (and vchild (pos? (:w vsize)) (pos? (:h vsize)) (pos? (:w cr)) (pos? (:h cr)))
                           (let [shifted (translate-placed vchild (- (:x scroll)) (- (:y scroll)))
                                 vbuf    (render-buffer shifted (:h cr) (:w cr))]
                             (blit buf vbuf 0 0 (:w cr) (:h cr) (:x cr) (:y cr) content-clip))
                           buf)]
          buf)

        :modal
        ;; A modal is opaque: it fills its whole rect (with spaces, clearing any base UI painted
        ;; beneath it) before drawing its border/title and children, so the overlay reads cleanly
        ;; on top of whatever the driver painted first.
        (let [buf (fill-rect buffer rect style node-clip)
              buf (if (:border? attrs) (draw-border buf rect style node-clip) buf)
              buf (if-let [title (:title attrs)]
                    (put-str buf (+ (:x rect) 2) (:y rect) (str " " title " ") style node-clip)
                    buf)]
          (reduce (fn [b child] (paint b child node-clip)) buf children))

        (:box :vbox :hbox)
        (let [buf (if (needs-bg-fill? style) (fill-rect buffer cr style content-clip) buffer)
              buf (if (:border? attrs) (draw-border buf rect style node-clip) buf)]
          (reduce (fn [b child] (paint b child node-clip)) buf children))

        buffer))))

(defmethod paint :default [buffer node clip]
  ;; Built-in tags (and unregistered custom tags) route here. The `p` per-tag profiling wraps EVERY
  ;; built-in node; a custom tag's own `defmethod` may add its own `p` if it wants profiling.
  (p (paint-id (::tag node))
    (internal-paint buffer node clip)))

(>defn render-buffer
  "Returns a fresh `rows`x`cols` buffer with the placed tree rooted at `placed-root` painted into it.
Painting walks the tree in order (painter's algorithm), clipping every write to the screen bounds."
  [placed-root rows cols]
  [::node nat-int? nat-int? => ::buffer]
  (paint (make-buffer rows cols) placed-root {:x 0 :y 0 :w cols :h rows}))

;; ============================================================================
;; Render — screen inspection
;; ============================================================================

(>defn- continuation-cell?
  "Returns true if `cell` is a wide-char continuation marker: a space whose preceding cell `prev` holds
a 2-column character."
  [prev cell]
  [(? ::cell) ::cell => boolean?]
  (boolean
    (and prev
      (= \space (:ch cell))
      (= 2 (code-point-width (int (:ch prev)))))))

(>defn screen
  "Returns a vector of `rows` strings, one per buffer row, formed by joining each row's cell
characters. Wide-char continuation cells (the blank that follows a 2-column character) are dropped
so the strings read naturally."
  [buffer]
  [::buffer => (s/coll-of string? :kind vector?)]
  (let [{:keys [rows cols cells]} buffer]
    (mapv
      (fn [row]
        (let [start     (* row cols)
              row-cells (subvec cells start (+ start cols))]
          (apply str
            (keep-indexed
              (fn [i cell]
                (when-not (continuation-cell? (when (pos? i) (nth row-cells (dec i))) cell)
                  (:ch cell)))
              row-cells))))
      (range rows))))

(>defn screen-styled
  "Returns a vector (one per buffer row) of vectors of cell maps `{:ch :sgr}`, exposing the full styled
contents of `buffer` for fine-grained assertions."
  [buffer]
  [::buffer => (s/coll-of (s/coll-of ::cell :kind vector?) :kind vector?)]
  (let [{:keys [rows cols cells]} buffer]
    (mapv
      (fn [row] (let [start (* row cols)] (subvec cells start (+ start cols))))
      (range rows))))

;; ============================================================================
;; Render — diff → ops → ANSI
;; ============================================================================

(>def ::row nat-int?)
(>def ::col nat-int?)
(>def ::text string?)
(>def ::sgr-codes (s/coll-of nat-int? :kind vector?))
;; NOTE: an op's :sgr value is a vector of SGR integer codes (not a ::style map). Because s/keys
;; validates any present key against the spec registered under its unqualified name (and ::sgr is a
;; style map), we spec ::op explicitly rather than via s/keys so the :sgr field is checked as a codes
;; vector.
(>def ::op
  (s/and map?
    #(nat-int? (:row %))
    #(nat-int? (:col %))
    #(string? (:text %))
    #(s/valid? ::sgr-codes (:sgr %))))
(>def ::ops (s/coll-of ::op :kind vector?))

(>defn- same-dims?
  "Returns true if buffers `a` and `b` have identical row and column counts."
  [a b]
  [::buffer ::buffer => boolean?]
  (and (= (:rows a) (:rows b)) (= (:cols a) (:cols b))))

(>defn- row-ops
  "Returns the vector of run ops for a single `row` of `next-buf`, comparing against `prev-cells` (the
same row of the previous buffer, or `nil` for a full repaint). Adjacent changed cells that share a
style are coalesced into one op; on a full repaint every non-default cell is emitted (still
coalesced)."
  [row cols next-cells prev-cells]
  [nat-int? nat-int? ::cells (? ::cells) => ::ops]
  (p `row-ops
   (let [start (* row cols)]
    (loop [col 0, run nil, out []]
      (let [flush (fn [out run] (if run (conj out run) out))]
        (if (< col cols)
          (let [idx      (+ start col)
                cell     (nth next-cells idx)
                prev     (when prev-cells (nth prev-cells idx))
                changed? (if prev-cells
                           (not= cell prev)
                           (not= cell blank-cell))
                codes    (style->sgr-codes (:sgr cell))]
            (if changed?
              (if (and run (= (:sgr run) codes))
                (recur (inc col) (update run :text str (:ch cell)) out)
                (recur (inc col)
                  {:row row :col col :sgr codes :text (str (:ch cell))}
                  (flush out run)))
              (recur (inc col) nil (flush out run))))
          (flush out run)))))))

(>defn diff
  "Returns a vector of run ops describing how to turn buffer `prev` into buffer `next`. Each op is
`{:row r :col c :sgr <codes-vector> :text \"...\"}`; horizontally adjacent changed cells sharing a
style are coalesced into a single op and unchanged cells produce no ops. When `prev` is `nil` or has
different dimensions than `next`, a full repaint is emitted (every non-default cell, still
coalesced per row)."
  [prev next]
  [(? ::buffer) ::buffer => ::ops]
  (p `diff
    (let [{:keys [rows cols cells]} next
          full?      (or (nil? prev) (not (same-dims? prev next)))
          prev-cells (when-not full? (:cells prev))]
      (into []
        (mapcat (fn [row] (row-ops row cols cells prev-cells)))
        (range rows)))))

(>defn- ops->ansi*
  "Serializes run `ops` to a single ANSI string; see `ops->ansi` for the full contract."
  [ops]
  [::ops => string?]
  (let [{:keys [out pen]}
        (reduce
          (fn [{:keys [out pen]} {:keys [row col sgr text]}]
            (let [move   (str "[" (inc row) ";" (inc col) "H")
                  sgr?   (not= pen sgr)
                  ;; SGR codes are additive on the wire, so turning an attribute OFF (a code in
                  ;; `pen` that is absent from `sgr`) needs an explicit reset first — otherwise it
                  ;; leaks into this run (e.g. reverse video bleeding from a newly-focused element
                  ;; onto the unfocused one to its right). Pure additions (pen ⊆ sgr) need no
                  ;; reset; a change to the default style already emits a reset via `sgr-string`.
                  reset? (and (seq sgr) (not (every? (set sgr) pen)))]
              {:out (str out move
                      (when sgr? (str (when reset? (sgr-string [])) (sgr-string sgr)))
                      text)
               :pen sgr}))
          {:out "" :pen []}
          ops)]
    (if (seq pen) (str out (sgr-string [])) out)))

(>defn ops->ansi
  "Returns a single ANSI string that applies the run `ops` to a terminal. Each op emits a cursor move
`\"\\u001b[<row+1>;<col+1>H\"`, an SGR sequence only when the pen style changes from the previous
op, then the op's text. A trailing reset (`\"\\u001b[0m\"`) is emitted when the final pen style is
non-default."
  [ops]
  [::ops => string?]
  (p `ops->ansi (ops->ansi* ops)))

(>defn frame->ansi
  "Returns the ANSI string to render the transition from buffer `prev` to buffer `next`, by diffing
them and serializing the ops. When `:sync?` in `opts` is true the whole sequence is wrapped in DEC
private mode 2026 (`\"\\u001b[?2026h\"` … `\"\\u001b[?2026l\"`) so the terminal applies it as a
single atomic frame; otherwise no wrapper is added. When `:clear?` in `opts` is true a clear-screen
plus cursor-home is prepended to the body — used on a resize repaint, where a plain full repaint only
writes non-blank cells and would otherwise leave stale content from the previous size on screen."
  [prev next opts]
  [(? ::buffer) ::buffer (s/keys :opt-un [::sync? ::clear?]) => string?]
  (let [body (ops->ansi (diff prev next))
        body (if (:clear? opts) (str "[2J[H" body) body)]
    (if (:sync? opts)
      (str "[?2026h" body "[?2026l")
      body)))

(>def ::sync? boolean?)
(>def ::clear? boolean?)

;; ============================================================================
;; Components & walker
;; ============================================================================
;;
;; This section provides a React-free component model for the TUI target. A
;; component *class* is a faux Fulcro class (a plain map carrying `:fulcro$options`,
;; built via `rc/configure-anonymous-component!`) and a component *instance* is a
;; plain map mirroring the CLJ shape produced by `components`' `create-element`:
;;
;;   {:fulcro$isComponent true
;;    :fulcro$class       <class>
;;    :props              {:fulcro$value <props-map>
;;                         :fulcro$app   <app>
;;                         :fulcro$reactKey <key>}} ; reactKey only when present
;;
;; These instances are understood by `rc/props`, `rc/get-computed`, `rc/get-ident`,
;; and `rc/component-options`, so user render functions can use the normal raw API.

;; Component *instances* are built with Fulcro's own `comp/factory`/`comp/computed-factory`.
;; In CLJ (and babashka) those produce a plain raw-component instance map (see
;; `com.fulcrologic.fulcro.components/create-element`), recognized by `rc/component-instance?`
;; and readable via `rc/props`/`rc/get-computed`/`rc/component-options` — exactly what the walker
;; (`render-tree`) needs. We therefore do NOT define our own factory; we just bind Fulcro's
;; render-time dynamic vars (`comp/*app*`/`comp/*parent*`/`comp/*shared*`) around the walk, the same
;; way `com.fulcrologic.fulcro.application/mount!` does, so the app/shared are stamped onto instances.

(>def ::component-class rc/component-class?)
(>def ::component-instance rc/component-instance?)

(>defn render-instance
  "Returns the node (or vector of nodes/strings/numbers) produced by calling the
`:render` of the component `instance`'s class. Returns `nil` if the class has no
`:render`."
  [instance]
  [::component-instance => any?]
  (when-let [render (rc/component-options instance :render)]
    (render instance)))

(declare render-tree)

(>defn- render-children
  "Returns a vector of the results of `render-tree` over each child in `children`,
dropping `nil` results and splicing vector results in as siblings. Each child is rendered with
`hooks/*child-index*` bound to its positional index so that the hook render-path of a child
COMPONENT is stable across renders (this is what makes `use-state` etc. work — see `render-tree`)."
  [children]
  [sequential? => vector?]
  (let [idx (volatile! -1)]
    (persistent!
      (reduce
        (fn [acc c]
          (vswap! idx inc)
          (let [r (binding [hooks/*child-index* (atom @idx)] (render-tree c))]
            (cond
              (nil? r) acc
              (vector? r) (reduce conj! acc r)
              :else (conj! acc r))))
        (transient [])
        children))))

(>defn render-tree
  "Returns a pure TUI node tree for `x`, recursively replacing every component
instance with the node tree its render produces. The result contains no component
instances and is suitable to hand to `place`. Each kind of `x` is handled as:

* a TUI node (`node?`) - recurse into its `::children` (rendering each child),
keeping the node's tag/attrs;
* a component instance (`rc/component-instance?`) - bind `comp/*parent*` to it, call its
`:render`, then recurse into the returned node (or splice a returned vector of
siblings);
* a string or number - returned unchanged;
* `nil` - returned as `nil` (callers/`render-children` drop it);
* a sequential collection - rendered element-wise and returned as a vector of
siblings (spliced by the caller).

When the render of a component yields several siblings, this returns a vector of
nodes; otherwise it returns a single node (or scalar)."
  [x]
  [any? => any?]
  (p ::render-tree
    (cond
      (nil? x) nil

      (node? x)
      (assoc x ::children (render-children (::children x)))

      (rc/component-instance? x)
      ;; Establish the hook render context for this component (mirrors c.f.f.headless): a stable
      ;; render-path (parent-path + this component's react-key or positional child index) plus fresh
      ;; per-component hook/child indices. With this bound, `hooks/use-state` (and friends) persist
      ;; component-local state in the app runtime atom keyed by path — so it survives the fact that
      ;; every render rebuilds the component instance — and is naturally distinct per to-many row.
      (let [child-idx (when hooks/*child-index* @hooks/*child-index*)
            react-key (some-> x :props :fulcro$reactKey)
            segment   (if react-key [:key react-key] (or child-idx 0))
            new-path  (conj (or hooks-ctx/*current-path* []) segment)]
        (binding [comp/*parent*            x
                  hooks-ctx/*current-path* new-path
                  hooks/*hook-index*       (atom 0)
                  hooks/*child-index*      (atom -1)]
          (hooks/record-rendered-path! new-path)
          (let [output (render-instance x)]
            (hooks/mark-mounted! new-path)
            (cond
              (nil? output) nil
              (vector? output) (render-children output)
              :else (render-tree output)))))

      (or (string? x) (number? x)) x

      (sequential? x) (render-children x)

      :else x)))

(>defn render-root
  "Returns the pure TUI node tree for a root component `class` given its `props` tree.
Builds a root instance via `(comp/factory class)` and walks it with `render-tree`. Binds
Fulcro's render-time dynamic vars (`comp/*app*`/`comp/*parent*`/`comp/*shared*`) around the
walk — the same vars `com.fulcrologic.fulcro.application/mount!` binds during a React render —
so the app and shared props are stamped onto the instances the factories create."
  ([class props] [::component-class map? => any?] (render-root class props nil))
  ([class props app]
   [::component-class map? any? => any?]
   ;; Root of the hook render context (mirrors c.f.f.headless/render-app-tree): start the render-path at
   ;; [], give this frame fresh effect/rendered-path collectors, then after the walk run any scheduled
   ;; effects and unmount (clean up) the hook state of components that did not render this frame.
   (let [rt-atom    (:com.fulcrologic.fulcro.application/runtime-atom app)
         prev-paths (set (keys (get (some-> rt-atom deref) ::hooks/hook-registry)))]
     (binding [comp/*app*               app
               comp/*parent*            nil
               comp/*shared*            (some-> app comp/shared)
               hooks-ctx/*current-path* []
               hooks/*hook-index*       (atom 0)
               hooks/*child-index*      (atom -1)
               hooks/*pending-effects*  (atom [])
               hooks/*rendered-paths*   (atom #{})]
       (let [tree (render-tree ((comp/factory class) props))]
         (hooks/cleanup-unmounted-components! prev-paths @hooks/*rendered-paths*)
         (hooks/run-pending-effects!)
         tree)))))

;; ----------------------------------------------------------------------------
;; Node-query / interaction utilities
;; ----------------------------------------------------------------------------

(>defn node-attr
  "Returns the value of attribute `k` on TUI `node` (from its `::attrs`), or `nil` if
`node` is not a node or lacks the attribute."
  [node k]
  [any? any? => any?]
  (when (node? node) (get (::attrs node) k)))

(>defn find-by-id
  "Returns the first node (depth-first, pre-order) within `node` whose `:id` attribute
equals `id`, or `nil` if none is found. Strings/numbers and non-node children are
skipped. `node` may itself be the match."
  [node id]
  [any? any? => (? ::node)]
  (when (node? node)
    (if (= id (node-attr node :id))
      node
      (some #(find-by-id % id) (::children node)))))

(>defn viewport?
  "Returns true if `node` is a `:viewport` node."
  [node]
  [any? => boolean?]
  (and (node? node) (= :viewport (::tag node))))

(>defn content-view-size
  "Returns the content-area size `{:w :h}` of a placed `node`: its `::rect` size shrunk by the edge
insets implied by its attrs (`:border?`/`:padding`). This is the visible window size of a viewport."
  [node]
  [::node => ::size]
  (let [r (::rect node)
        e (+ (long (or (:padding (::attrs node)) 0)) (if (:border? (::attrs node)) 1 0))]
    {:w (max 0 (- (:w r) e e))
     :h (max 0 (- (:h r) e e))}))

(>defn placed-viewports
  "Returns a vector of every placed `:viewport` node found (depth-first, pre-order) within the placed
`tree`, including any nested inside another viewport's virtual content subtree (`::viewport-content`).
Each returned node carries its `::rect`, `::virtual-size`, `::scroll`, and `::viewport-content`."
  [tree]
  [any? => vector?]
  (let [out (volatile! (transient []))]
    (letfn [(walk [x]
              (when (node? x)
                (when (viewport? x) (vswap! out conj! x))
                (doseq [c (::children x)] (walk c))
                (when-let [vc (::viewport-content x)] (walk vc))))]
      (walk tree))
    (persistent! @out)))

(>defn focus-viewport-context
  "Returns `{:viewport <placed-viewport-node> :virtual-rect <rect>}` describing the innermost placed
`:viewport` in `placed-tree` whose virtual content subtree (`::viewport-content`) contains the node
with `:id` `focus-id`, along with that focused node's VIRTUAL `::rect` (0-based within the viewport).
Returns `nil` when `focus-id` is not inside any viewport. When viewports are nested, the innermost
enclosing viewport is returned."
  [placed-tree focus-id]
  [any? any? => (? map?)]
  (let [result (volatile! nil)]
    (letfn [(walk [x]
              (when (and (nil? @result) (node? x))
                (when (viewport? x)
                  (when-let [hit (find-by-id (::viewport-content x) focus-id)]
                    ;; descend first to prefer an innermost nested viewport
                    (walk (::viewport-content x))
                    (when (nil? @result)
                      (vreset! result {:viewport x :virtual-rect (::rect hit)}))))
                (doseq [c (::children x)]
                  (when (nil? @result) (walk c)))))]
      (walk placed-tree))
    @result))

(>defn scroll-to-show
  "Returns the new scroll offset `{:x :y}` for a viewport so that the focused node's `virtual-rect`
becomes visible within the `view-size` `{:w :h}` content window, given the current `scroll` `{:x :y}`.
Performs the MINIMAL scroll on each axis: if the rect is above/left of the window, scroll back to its
near edge; if below/right, scroll forward so its far edge is the last visible cell; otherwise leave
that axis unchanged. Does not clamp to the virtual size (callers clamp via `clamp-scroll`). Pure."
  [scroll virtual-rect view-size]
  [::scroll ::rect ::size => ::scroll]
  (let [adjust (fn [s near extent view]
                 (let [far (+ near extent)]
                   (cond
                     ;; rect's near edge is above/left of the window — scroll back to it
                     (< near s) near
                     ;; rect's far edge is below/right of the window — scroll forward minimally so
                     ;; the far edge is the last visible cell (unless the rect is taller/wider than the
                     ;; window, in which case show its near edge)
                     (> far (+ s view)) (if (> extent view) near (- far view))
                     :else s)))]
    {:x (adjust (long (:x scroll)) (:x virtual-rect) (:w virtual-rect) (:w view-size))
     :y (adjust (long (:y scroll)) (:y virtual-rect) (:h virtual-rect) (:h view-size))}))

(>defn node-text
  "Returns the concatenated text of the `node` subtree: the string/number children of
the node and, recursively, of all of its descendant nodes, joined left-to-right.
Non-node, non-text children contribute nothing. A bare string/number returns its
own string."
  [node]
  [any? => string?]
  (cond
    (string? node) node
    (number? node) (str node)
    (node? node) (apply str (map node-text (::children node)))
    :else ""))

(>defn activate!
  "Invokes the `:on-activate` handler attribute of TUI `node` (if present) with no
arguments and returns its result. Returns `nil` when there is no handler. Used to
simulate activating a button/control."
  [node]
  [any? => any?]
  (when-let [handler (node-attr node :on-activate)]
    (handler)))

(>defn press!
  "Invokes the `:on-key` handler attribute of TUI `node` (if present) with the key
`k` and returns its result. Returns `nil` when there is no handler. Used to
simulate a key press delivered to a focused node."
  [node k]
  [any? any? => any?]
  (when-let [handler (node-attr node :on-key)]
    (handler k)))

(>defn type!
  "Invokes the `:on-change` handler attribute of TUI `node` (if present) with the
string `s` and returns its result. Returns `nil` when there is no handler. Used to
simulate typing the proposed value `s` into an input."
  [node s]
  [any? string? => any?]
  (when-let [handler (node-attr node :on-change)]
    (handler s)))

;; ============================================================================
;; Focus, input & key dispatch
;; ============================================================================
;;
;; This section adds the interactive layer to the TUI target: a focus model, a
;; focus ring (Tab/Shift-Tab navigation), controlled-input text editing with a
;; transient caret store, key routing (bubbling) with a global keymap, and the
;; single-step driver `process-key!`.
;;
;; State locations (single source of truth):
;;   * Focus     — the focused node's `:id` lives in the app STATE-MAP at `::focus`.
;;   * Caret store — transient, in the app RUNTIME-ATOM at `::carets`, a map of
;;                   `{input-id caret-index}`. NOT in the normalized db.
;;
;; A *key event* is a plain map produced by `tui.terminal` (we operate on it
;; structurally and never require that namespace):
;;
;;   {:key <kw-or-1-char-string> :char <str|nil> :ctrl? <bool> :alt? <bool>
;;    :shift? <bool> :raw <any>}
;;
;; Special `:key` values are `:enter :tab :escape :backspace :delete :up :down
;; :left :right :home :end :page-up :page-down :backtab`. A printable key has
;; `:key` = `:char` = the 1-character string.
;;
;; Handler-arg convention (matches `activate!`/`press!`/`type!`):
;;   * `:on-activate`    — `(handler)`            (no args)
;;   * `:on-key`         — `(handler key-event)`  (the event map)
;;   * `:on-change`      — `(handler value caret)`(new value, new caret)
;;   * `:on-submit`      — `(handler value)`      (the input's current value)
;;   * `:on-focus`       — `(handler id)`         (the id gaining focus)
;;   * `:on-lost-focus`  — `(handler id)`         (the id losing focus)

(>def ::focus (? any?))
(>def ::carets (? map?))

;; A key event map. We only constrain the keys we read; the map is open.
(>def ::key-event
  (s/keys :opt-un []))

(>def ::focus-id (? any?))

(def special-keys
  "The set of recognized non-printable `:key` values in a key event."
  #{:enter :tab :escape :backspace :delete :up :down :left :right
    :home :end :page-up :page-down :backtab})

;; ----------------------------------------------------------------------------
;; Focus primitives & dynamic var
;; ----------------------------------------------------------------------------

(def ^:dynamic *current-focus*
  "The `:id` of the currently focused node, bound by the walker/driver during a
   render so that render code can call `focused?`. Defaults to `nil`."
  nil)

(>defn current-focus
  "Returns the currently focused node `:id` from `app-or-state`. Accepts either a
Fulcro app (reads its state-atom) or a raw state-map. Returns `nil` when nothing
is focused."
  [app-or-state]
  [any? => any?]
  (let [state-map (if (and (map? app-or-state)
                        (contains? app-or-state :com.fulcrologic.fulcro.application/state-atom))
                    (some-> app-or-state :com.fulcrologic.fulcro.application/state-atom deref)
                    app-or-state)]
    (get state-map ::focus)))

(def ^:dynamic *suppress-render*
  "When true, render-triggering side effects (e.g. `focus!`'s `schedule-render!`) are SKIPPED because
   the caller is about to render once after a batch of state changes. The driver binds this true
   around `dispatch-key!` so a single keystroke that moves focus AND adjusts viewport scroll renders
   ONE frame (at the end of dispatch) instead of one frame per mutation — eliminating a redundant
   full tree build + paint per keypress. Default false, so a standalone `focus!` (no driver loop)
   still repaints immediately."
  false)

(>defn focus!
  "Sets the focused node `:id` to `id` in the app's state-map at `::focus` (the
single source of truth) via a direct `swap!`. If the app declares a renderer
(`:com.fulcrologic.fulcro.application/render-root!`/`schedule-render!`) it triggers
a render so the change is reflected on screen, but it remains usable without a
terminal. Returns the app.

The render is skipped when `*suppress-render*` is bound true (the driver batches a keystroke's
mutations into a single post-dispatch render); the focus state change still happens."
  [app id]
  [any? any? => any?]
  (when-let [state-atom (:com.fulcrologic.fulcro.application/state-atom app)]
    (swap! state-atom assoc ::focus id))
  (when-not *suppress-render*
    (try
      (rapp/schedule-render! app)
      (catch Throwable _ nil)))
  app)

;; ----------------------------------------------------------------------------
;; Viewport scroll state (state-map: ::scroll → {viewport-id {:x :y}})
;; ----------------------------------------------------------------------------

(>defn all-scroll
  "Returns the whole viewport-scroll map `{viewport-id {:x :y}}` from `app-or-state` (the state-map
key `::scroll`), or `{}` when none is recorded. Accepts a Fulcro app (reads its state-atom) or a
raw state-map."
  [app-or-state]
  [any? => map?]
  (let [state-map (if (and (map? app-or-state)
                        (contains? app-or-state :com.fulcrologic.fulcro.application/state-atom))
                    (some-> app-or-state :com.fulcrologic.fulcro.application/state-atom deref)
                    app-or-state)]
    (or (get state-map ::scroll) {})))

(>defn viewport-scroll
  "Returns the scroll offset `{:x :y}` recorded for the viewport with id `vp-id` in `app-or-state`
(under the state-map key `::scroll`), defaulting to `{:x 0 :y 0}` when none is recorded."
  [app-or-state vp-id]
  [any? any? => ::scroll]
  (or (get (all-scroll app-or-state) vp-id) {:x 0 :y 0}))

(>defn set-viewport-scroll!
  "Sets the scroll offset `{:x :y}` for the viewport with id `vp-id` in `app`'s state-map (under
`::scroll`) via a direct `swap!`. Returns `app`."
  [app vp-id scroll]
  [any? any? ::scroll => any?]
  (when-let [state-atom (:com.fulcrologic.fulcro.application/state-atom app)]
    (swap! state-atom assoc-in [::scroll vp-id] scroll))
  app)

;; ----------------------------------------------------------------------------
;; Focus ring (pure)
;; ----------------------------------------------------------------------------

(>defn focusable-node?
  "Returns true if `node` can receive focus. A node is focusable when it has an
`:id` attribute AND either: its attrs set `:focusable? true`, its tag is `:input`
or `:button`, or it carries any of the focus-relevant handler attributes
(`:on-activate`, `:on-change`, `:on-focus`, `:on-lost-focus`).

`:on-key` is deliberately NOT a focus trigger: an `:on-key` handler receives keys by
bubbling from the focused descendant up through its ancestors (see `route-key`), so a
container that only routes keys is a passive key-router, not a focus stop. Making such a
container focusable would put a useless Tab stop on its (non-interactive) corner. A node that
genuinely needs to be focused for its own key handling must opt in with `:focusable? true`."
  [node]
  [any? => boolean?]
  (boolean
    (and (node? node)
      (some? (node-attr node :id))
      (let [{::keys [tag attrs]} node]
        (or (:focusable? attrs)
          (#{:input :button} tag)
          (some attrs [:on-activate :on-change :on-focus :on-lost-focus]))))))

(>defn focusables
  "Returns an ordered vector of focusable descriptors for every focusable node in
`node-tree`, in document (pre-order, depth-first) order. Each descriptor is a map
`{:id :priority :dfs :node}` where `:priority` is the node's `:priority` attr
(default 0) and `:dfs` is the node's pre-order index among all visited nodes."
  [node-tree]
  [any? => vector?]
  (p ::focusables
    (let [out (volatile! (transient []))
          idx (volatile! 0)]
      (letfn [(walk [x]
                (when (node? x)
                  (let [dfs @idx]
                    (vswap! idx inc)
                    (when (focusable-node? x)
                      (vswap! out conj!
                        {:id       (node-attr x :id)
                         :priority (long (or (node-attr x :priority) 0))
                         :dfs      dfs
                         :node     x}))
                    (doseq [c (::children x)]
                      (walk c)))))]
        (walk node-tree))
      (persistent! @out))))

(>defn focus-order
  "Returns `focusables` sorted into focus-traversal order: by `:priority`
descending, then by `:dfs` (document order) ascending."
  [focusables]
  [vector? => vector?]
  (vec (sort-by (juxt #(- (:priority %)) :dfs) focusables)))

(>defn- neighbor-id
  "Returns the id of the focusable neighbor of `current-id` within ordered `order`,
stepping by `step` (+1 for next, -1 for previous), wrapping around. Returns the
first id (or `nil`) when `current-id` is absent/nil or `order` is empty."
  [order current-id step]
  [vector? any? int? => any?]
  (let [n (count order)]
    (when (pos? n)
      (let [ids (mapv :id order)
            pos (.indexOf ^java.util.List ids current-id)]
        (if (neg? pos)
          (first ids)
          (nth ids (mod (+ pos step) n)))))))

(>defn next-focus
  "Returns the id of the next focusable after `current-id` in `order` (the result of
`focus-order`), wrapping to the first. When `current-id` is absent or `nil`,
returns the first id. Returns `nil` when `order` is empty."
  [order current-id]
  [vector? any? => any?]
  (neighbor-id order current-id 1))

(>defn prev-focus
  "Returns the id of the previous focusable before `current-id` in `order` (the result
of `focus-order`), wrapping to the last. When `current-id` is absent or `nil`,
returns the first id. Returns `nil` when `order` is empty."
  [order current-id]
  [vector? any? => any?]
  (neighbor-id order current-id -1))

;; ----------------------------------------------------------------------------
;; Focus transition
;; ----------------------------------------------------------------------------

(declare flush-pending-change! clear-input-buffer!)

(>defn apply-focus-change!
  "Fires focus-transition handlers when focus moves from `old-id` to `new-id` within
`node-tree`. When the ids differ, the node with `old-id` has its `:on-lost-focus`
handler invoked with `old-id`, and the node with `new-id` has its `:on-focus`
handler invoked with `new-id` (both found via `find-by-id`, matching the
interaction-util handler-arg convention). Returns `app`. A no-op when the ids are
equal.

For a buffered input (`:change-debounce-ms`), losing focus first flushes any pending
debounced `:on-change` and drops its value buffer, so the app sees the final text
immediately and controlled semantics resume (the prop is authoritative while blurred)."
  [app node-tree old-id new-id]
  [any? any? any? any? => any?]
  (when (not= old-id new-id)
    (when (some? old-id)
      (flush-pending-change! app old-id)
      (clear-input-buffer! app old-id)
      (when-let [h (node-attr (find-by-id node-tree old-id) :on-lost-focus)]
        (h old-id)))
    (when (some? new-id)
      (when-let [h (node-attr (find-by-id node-tree new-id) :on-focus)]
        (h new-id))))
  app)

;; ----------------------------------------------------------------------------
;; Programmatic focus helpers (containers + focus groups)
;; ----------------------------------------------------------------------------

(>defn- first-focusable-of
  "Returns the id of the first focusable (in focus-traversal order) within `node`'s subtree, or nil."
  [node]
  [any? => any?]
  (:id (first (focus-order (focusables node)))))

(>defn- last-focusable-of
  "Returns the id of the last focusable (in focus-traversal order) within `node`'s subtree, or nil."
  [node]
  [any? => any?]
  (:id (peek (focus-order (focusables node)))))

(>defn first-focusable-in
  "Returns the id of the first focusable within the subtree rooted at the node with `container-id` in
`tree` (focus-traversal order), or nil when the container is absent or has no focusables."
  [tree container-id]
  [any? any? => any?]
  (some-> (find-by-id tree container-id) first-focusable-of))

(>defn last-focusable-in
  "Returns the id of the last focusable within the subtree rooted at the node with `container-id` in
`tree` (focus-traversal order), or nil. Because to-many subforms append new children, this lands on
the most-recently-added item when given the items' container id."
  [tree container-id]
  [any? any? => any?]
  (some-> (find-by-id tree container-id) last-focusable-of))

(>defn focus-in!
  "Sets focus in `app` to `new-id`, firing `:on-lost-focus`/`:on-focus` transitions against `tree`
(pairs `focus!` with `apply-focus-change!`). Returns `new-id`; a no-op when `new-id` is nil."
  [app tree new-id]
  [any? any? any? => any?]
  (when (some? new-id)
    (let [old (current-focus app)]
      (focus! app new-id)
      (apply-focus-change! app tree old new-id)))
  new-id)

(>defn focus-first-in!
  "Moves focus to the first focusable within the `container-id` subtree of `tree` (see
`first-focusable-in`), firing transitions. Returns the focused id, or nil."
  [app tree container-id]
  [any? any? any? => any?]
  (focus-in! app tree (first-focusable-in tree container-id)))

(>defn focus-last-in!
  "Moves focus to the last focusable within the `container-id` subtree of `tree` (see
`last-focusable-in`), firing transitions. Use after adding a to-many child to focus the new item.
Returns the focused id, or nil."
  [app tree container-id]
  [any? any? any? => any?]
  (focus-in! app tree (last-focusable-in tree container-id)))

(>defn- nodes-with-attr
  "Returns the vector of nodes in `tree` (pre-order, depth-first) whose attr `k` equals `v`."
  [tree k v]
  [any? any? any? => vector?]
  (let [out (volatile! (transient []))]
    (letfn [(walk [x]
              (when (node? x)
                (when (= v (node-attr x k)) (vswap! out conj! x))
                (doseq [c (::children x)] (walk c))))]
      (walk tree))
    (persistent! @out)))

(>defn focus-group-step!
  "Moves focus among the members of focus group `group` in `tree`, stepping by `step` (+1 next, -1
previous) and wrapping. A group member is any node carrying `:focus-group group`; focus lands on that
member's first focusable descendant, skipping the members' inner fields. The current member is the
one whose subtree contains the focused node; when focus is outside the group, moves to the first
member. Returns the newly focused id, or nil when the group has no focusable members."
  [app tree group step]
  [any? any? any? int? => any?]
  (let [paired (into []
                 (keep (fn [m] (when-let [s (first-focusable-of m)] {:member m :stop s})))
                 (nodes-with-attr tree :focus-group group))]
    (when (seq paired)
      (let [cur     (current-focus app)
            cur-idx (first (keep-indexed (fn [i {:keys [member]}]
                                           (when (find-by-id member cur) i))
                             paired))
            n       (count paired)
            target  (:stop (if cur-idx (nth paired (mod (+ cur-idx step) n)) (first paired)))]
        (focus-in! app tree target)))))

(>defn focus-next-in-group!
  "Moves focus to the next member of focus group `group` (see `focus-group-step!`). Returns the
newly focused id, or nil."
  [app tree group]
  [any? any? any? => any?]
  (focus-group-step! app tree group 1))

(>defn focus-prev-in-group!
  "Moves focus to the previous member of focus group `group` (see `focus-group-step!`). Returns the
newly focused id, or nil."
  [app tree group]
  [any? any? any? => any?]
  (focus-group-step! app tree group -1))

;; ----------------------------------------------------------------------------
;; Multiline caret <-> (row, col) mapping (pure)
;; ----------------------------------------------------------------------------
;;
;; A multiline input's `:value` is a string that may contain `\n`; its caret is a single 0-based
;; index into that string (a Java char index, consistent with `apply-edit`'s `subs`/`count`). When
;; the value is displayed it is wrapped to the input's width (via `wrap-text`), producing a grid of
;; visual rows. These functions map between the logical caret index and the visual (row, col).
;;
;; Wrap-boundary convention: a caret that sits exactly at a SOFT wrap point (the column where a line
;; wrapped because the next word did not fit, and where `wrap-text` dropped the separating space)
;; resolves to the END of the earlier visual row (row r, col = that row's length) rather than the
;; start of the next row. So the dropped-space positions all belong to the end of the row above them.

(>def ::layout-line (s/keys :req-un [::start ::len ::text]))
(>def ::start nat-int?)
(>def ::len nat-int?)
(>def ::wrap-layout (s/coll-of ::layout-line :kind vector?))

(>defn wrap-layout
  "Returns the visual-line layout of string `value` wrapped to `width` display columns: a vector of
`{:start :len :text}` maps, one per visual row, in order. `:text` is the row's wrapped string,
`:start` is the caret index (into `value`) of the row's first character, and `:len` is the number
of `value` characters the row's text spans. Characters dropped at a soft-wrap boundary (the
collapsed space between two wrapped words) and the hard `\\n` are NOT counted in any row's `:len`;
they live in the gap between one row's `:start + :len` and the next row's `:start`. Reuses
`wrap-text` so the rows match what `paint` displays."
  [value width]
  [string? int? => ::wrap-layout]
  (p ::wrap-layout
    (let [v    (str value)
          segs (str/split v #"\n" -1)]
      (loop [segs segs, base 0, out []]
        (if (seq segs)
          (let [seg     (first segs)
                lines   (wrap-text seg width)
                entries (loop [lines lines, pos 0, es []]
                          (if (seq lines)
                            (let [ln    (first lines)
                                  llen  (count ln)
                                  start (+ base pos)
                                  after (+ pos llen)
                                  ;; a soft break dropped the run of spaces between this row and the
                                  ;; next; skip them so the next row starts at the right caret index.
                                  skip  (if (next lines)
                                          (count (take-while #(= \space %) (subs seg after)))
                                          0)]
                              (recur (rest lines) (+ after skip)
                                (conj es {:start start :len llen :text ln})))
                            es))]
            ;; +1 for the hard newline that separated this segment from the next.
            (recur (rest segs) (+ base (count seg) 1) (into out entries)))
          out)))))

(>defn caret->rowcol
  "Returns the visual `[row col]` of caret index `caret` within the layout of `value` wrapped to
`width` columns. The caret is clamped into `[0, (count value)]`. At a soft-wrap boundary the caret
resolves to the END of the earlier row (see the wrap-boundary convention above). Pure."
  [value width caret]
  [string? int? int? => (s/tuple nat-int? nat-int?)]
  (let [layout (wrap-layout value width)
        n      (count (str value))
        c      (max 0 (min caret n))]
    (loop [i 0, ls layout]
      (if (seq ls)
        (let [{:keys [start len]} (first ls)
              last?      (nil? (next ls))
              next-start (if last? (inc (+ start len)) (:start (second ls)))]
          (if (or last? (< c next-start))
            [i (max 0 (min (- c start) len))]
            (recur (inc i) (rest ls))))
        [0 0]))))

(>defn rowcol->caret
  "Returns the caret index into `value` for the visual position `[row col]` in the layout of `value`
wrapped to `width` columns. `row` is clamped into the row range and `col` is clamped to the target
row's length, so an off-the-end position lands at that row's end. The inverse of `caret->rowcol`
(modulo the wrap-boundary convention). Pure."
  [value width row col]
  [string? int? int? int? => nat-int?]
  (let [layout (wrap-layout value width)
        nrows  (count layout)]
    (if (zero? nrows)
      0
      (let [r (max 0 (min row (dec nrows)))
            {:keys [start len]} (nth layout r)
            c (max 0 (min col len))]
        (+ start c)))))

(>defn text-scroll-top
  "Returns the internal top visual-line offset for a multiline input so that the caret's visual row is
visible within a `height`-row window, given the `value` wrapped to `width` columns and the current
`caret`. Performs minimal scrolling: if the caret row is above the current window it would scroll
to it; here, with no prior offset tracked, it returns the smallest non-negative top such that the
caret row lies in `[top, top+height)` and the window does not run past the last row unnecessarily.
Concretely it returns `(max 0 (min (- caret-row (dec height)) ...))` clamped so the caret row is the
last visible row when it would otherwise be below the window, and 0 when the caret row already fits
from the top. Pure."
  [value width caret height]
  [string? int? int? int? => nat-int?]
  (let [[row _] (caret->rowcol value width caret)
        h (max 1 height)]
    (cond
      (< row h) 0
      :else (inc (- row h)))))

;; ----------------------------------------------------------------------------
;; Controlled input editing (pure + store)
;; ----------------------------------------------------------------------------

(>defn apply-edit
  "Returns `{:value :caret}` after applying the editing `key-event` to controlled
input text `value` with the cursor at `caret` (a 0-based index, clamped into
`[0, (count value)]`). Handles:

* a printable key (`:char` is a 1-char string) — insert at the caret, caret += 1
* `:backspace` — delete the char left of the caret, caret -= 1
* `:delete`    — delete the char right of the caret, caret unchanged
* `:left`/`:right` — move the caret one cell (clamped)
* `:home`/`:end`   — move the caret to the start/end

Any other key leaves `value` and (clamped) `caret` unchanged. Pure."
  [value caret key-event]
  [string? int? map? => (s/keys :req-un [::value ::caret])]
  (let [v   (str value)
        n   (count v)
        c   (max 0 (min caret n))
        k   (:key key-event)
        chr (:char key-event)]
    (cond
      ;; printable insertion
      (and (string? chr) (= chr k) (pos? (count chr)))
      {:value (str (subs v 0 c) chr (subs v c)) :caret (+ c (count chr))}

      (= k :backspace)
      (if (pos? c)
        {:value (str (subs v 0 (dec c)) (subs v c)) :caret (dec c)}
        {:value v :caret c})

      (= k :delete)
      (if (< c n)
        {:value (str (subs v 0 c) (subs v (inc c))) :caret c}
        {:value v :caret c})

      (= k :left) {:value v :caret (max 0 (dec c))}
      (= k :right) {:value v :caret (min n (inc c))}
      (= k :home) {:value v :caret 0}
      (= k :end) {:value v :caret n}
      :else {:value v :caret c})))

(>defn apply-edit-multiline
  "Returns `{:value :caret}` after applying editing `key-event` to multiline input text `value` (a
string that may contain `\\n`) with the cursor at `caret`, given the input's display `width` (the
wrap width, used for visual-line navigation). `caret` is clamped into `[0, (count value)]`. Differs
from `apply-edit` for a single-line input in three ways:

* `:enter` inserts a newline (`\\n`) at the caret and advances it (it does NOT submit).
* `:up`/`:down` move the caret one VISUAL line (per the wrapped layout at `width`), preserving the
  current visual column as the target column (clamped to the destination row's length).
* `:home`/`:end` move to the start/end of the current VISUAL line (not the whole value).

Printable insertion, `:backspace`, `:delete`, and `:left`/`:right` behave as in `apply-edit`;
because `\\n` is an ordinary character of `value`, left/right and backspace/delete cross line
boundaries naturally. Any other key leaves `value` and (clamped) `caret` unchanged. Pure."
  [value caret width key-event]
  [string? int? int? map? => (s/keys :req-un [::value ::caret])]
  (let [v   (str value)
        n   (count v)
        c   (max 0 (min caret n))
        k   (:key key-event)
        chr (:char key-event)]
    (cond
      (= k :enter)
      {:value (str (subs v 0 c) "\n" (subs v c)) :caret (inc c)}

      (and (string? chr) (= chr k) (pos? (count chr)))
      {:value (str (subs v 0 c) chr (subs v c)) :caret (+ c (count chr))}

      (= k :backspace)
      (if (pos? c)
        {:value (str (subs v 0 (dec c)) (subs v c)) :caret (dec c)}
        {:value v :caret c})

      (= k :delete)
      (if (< c n)
        {:value (str (subs v 0 c) (subs v (inc c))) :caret c}
        {:value v :caret c})

      (= k :left) {:value v :caret (max 0 (dec c))}
      (= k :right) {:value v :caret (min n (inc c))}

      (= k :home)
      (let [[row _] (caret->rowcol v width c)]
        {:value v :caret (rowcol->caret v width row 0)})

      (= k :end)
      (let [[row _] (caret->rowcol v width c)
            len (:len (nth (wrap-layout v width) row))]
        {:value v :caret (rowcol->caret v width row len)})

      (= k :up)
      (let [[row col] (caret->rowcol v width c)]
        {:value v :caret (rowcol->caret v width (dec row) col)})

      (= k :down)
      (let [[row col] (caret->rowcol v width c)]
        {:value v :caret (rowcol->caret v width (inc row) col)})

      :else {:value v :caret c})))

(>defn get-caret
  "Returns the caret index stored for input `id` in `app`'s runtime caret store
(`::carets`), or `default` (the end of the value) when none is stored."
  [app id default]
  [any? any? int? => int?]
  (let [carets (some-> app :com.fulcrologic.fulcro.application/runtime-atom deref ::carets)]
    (long (get carets id default))))

(>defn set-caret!
  "Stores caret index `caret` for input `id` in `app`'s runtime caret store
(`::carets`) via `swap!` on the runtime atom. Returns `app`."
  [app id caret]
  [any? any? int? => any?]
  (when-let [ra (:com.fulcrologic.fulcro.application/runtime-atom app)]
    (swap! ra update ::carets assoc id caret))
  app)

(>defn clear-caret!
  "Removes any stored caret for input `id` from `app`'s runtime caret store
(`::carets`). Returns `app`."
  [app id]
  [any? any? => any?]
  (when-let [ra (:com.fulcrologic.fulcro.application/runtime-atom app)]
    (swap! ra update ::carets dissoc id))
  app)

(>def ::input-widths (? map?))

(>defn input-width
  "Returns the effective content width (in columns) recorded for multiline input `id` in `app`'s
runtime (`::input-widths`, populated by the driver during render), or `default` when none is
recorded. The width is used by `handle-input-key!`/the driver to wrap the value and run visual
caret navigation."
  [app id default]
  [any? any? int? => int?]
  (let [widths (some-> app :com.fulcrologic.fulcro.application/runtime-atom deref ::input-widths)]
    (long (get widths id default))))

(>defn set-input-width!
  "Records the effective content `width` (in columns) for multiline input `id` in `app`'s runtime
(`::input-widths`) via `swap!` on the runtime atom, so subsequent key handling wraps and navigates
at the same width the input is painted with. Returns `app`."
  [app id width]
  [any? any? int? => any?]
  (when-let [ra (:com.fulcrologic.fulcro.application/runtime-atom app)]
    (swap! ra update ::input-widths assoc id width))
  app)

;; ----------------------------------------------------------------------------
;; Buffered inputs (opt-in via the `:change-debounce-ms` input attr)
;; ----------------------------------------------------------------------------
;;
;; A fully controlled input pays for a round-trip through the app's `:on-change`
;; (usually a transaction plus whatever downstream work it triggers) on EVERY
;; keystroke before the typed character can echo. When an input declares
;; `:change-debounce-ms N` (N > 0) the engine instead:
;;
;;   * Echoes each edit immediately from a transient VALUE BUFFER in the runtime
;;     atom (`::input-buffers`, keyed by input id, like the caret store). The
;;     buffer is substituted into the node tree by `current-node-tree`, so
;;     layout, painting, and subsequent edits all see the buffered value.
;;   * Debounces `:on-change`: it fires with the latest value once no key has
;;     arrived for N ms (`::pending-changes` holds the cancellable timer).
;;   * Flushes the pending `:on-change` immediately — and DROPS the buffer — on
;;     blur (focus leaving the input) and on single-line `:enter` (before
;;     `:on-submit`), so app state is consistent whenever anything else runs.
;;
;; Reconciliation (the StringBufferedInput rule, adapted): each buffer entry
;; remembers `:based-on`, the prop `:value` it diverged from. At tree-build time,
;; if the node's prop now EQUALS the buffer (the debounced commit landed) the
;; buffer is dropped as redundant; if the prop changed to something ELSE (an
;; external mutation — a load, a reset) the buffer is dropped and the prop wins,
;; preserving controlled semantics. Otherwise the buffer overrides the prop.

(>def ::input-buffers (? map?))
(>def ::pending-changes (? map?))
(>def ::default-change-debounce-ms (? int?))

(>defn set-default-change-debounce-ms!
  "Sets the app-wide default `:change-debounce-ms` for ALL inputs (runtime atom,
`::default-change-debounce-ms`). An input's own `:change-debounce-ms` attr overrides it
(including an explicit `0` to opt a single input back into fully-controlled behavior).
Returns `app`."
  [app ms]
  [any? int? => any?]
  (when-let [ra (:com.fulcrologic.fulcro.application/runtime-atom app)]
    (swap! ra assoc ::default-change-debounce-ms ms))
  app)

(>defn default-change-debounce-ms
  "Returns the app-wide default `:change-debounce-ms` (see
`set-default-change-debounce-ms!`), or 0 when unset."
  [app]
  [any? => int?]
  (long (or (some-> app :com.fulcrologic.fulcro.application/runtime-atom deref
              ::default-change-debounce-ms)
          0)))

(>defn get-input-buffer
  "Returns the buffer entry `{:value s :based-on s}` for input `id` in `app`'s runtime
buffered-value store (`::input-buffers`), or nil."
  [app id]
  [any? any? => (? map?)]
  (some-> app :com.fulcrologic.fulcro.application/runtime-atom deref ::input-buffers (get id)))

(>defn set-input-buffer!
  "Stores buffer `entry` (`{:value s :based-on s}`) for input `id` in `app`'s runtime
buffered-value store (`::input-buffers`). Returns `app`."
  [app id entry]
  [any? any? map? => any?]
  (when-let [ra (:com.fulcrologic.fulcro.application/runtime-atom app)]
    (swap! ra update ::input-buffers assoc id entry))
  app)

(>defn clear-input-buffer!
  "Removes any buffered value for input `id` from `app`'s runtime store (`::input-buffers`).
Returns `app`."
  [app id]
  [any? any? => any?]
  (when-let [ra (:com.fulcrologic.fulcro.application/runtime-atom app)]
    (swap! ra update ::input-buffers dissoc id))
  app)

(defn- cancel-pending-change!
  "Cancels and removes the pending debounced `:on-change` for input `id`, returning the
removed entry (`{:token .. :future .. :on-change .. :value .. :caret ..}`) or nil."
  [app id]
  (when-let [ra (:com.fulcrologic.fulcro.application/runtime-atom app)]
    (let [[old _] (swap-vals! ra update ::pending-changes dissoc id)
          entry   (get-in old [::pending-changes id])]
      (when-let [f (:future entry)] (future-cancel f))
      entry)))

(>defn flush-pending-change!
  "If input `id` has a pending debounced `:on-change`, cancels its timer and invokes the
handler NOW with the buffered value/caret. Returns `app`."
  [app id]
  [any? any? => any?]
  (when-let [{:keys [on-change value caret]} (cancel-pending-change! app id)]
    (on-change value caret))
  app)

(defn- schedule-pending-change!
  "(Re)schedules input `id`'s `:on-change` to fire with `value`/`caret` after `ms` of key
silence. Cancels any prior pending change for the id. The timer identifies its own entry
by token, so a stale timer that loses the race to a newer keystroke fires nothing."
  [app id ms on-change value caret]
  (cancel-pending-change! app id)
  (when-let [ra (:com.fulcrologic.fulcro.application/runtime-atom app)]
    (let [token (Object.)]
      (swap! ra update ::pending-changes assoc id
        {:token token :on-change on-change :value value :caret caret})
      (let [f (future
                (Thread/sleep (long ms))
                ;; Atomically claim our entry; fire only if it was still ours (not
                ;; cancelled/replaced while we slept).
                (let [[old _] (swap-vals! ra update ::pending-changes
                                (fn [pc] (if (identical? token (:token (get pc id)))
                                           (dissoc pc id)
                                           pc)))]
                  (when (identical? token (:token (get-in old [::pending-changes id])))
                    ;; This future is created during key dispatch, where the driver binds
                    ;; `*suppress-render*` true — and futures CONVEY dynamic bindings to
                    ;; their thread. Unbind it here or the commit's state change would
                    ;; never flag a repaint (the `:core-render!` hook checks it).
                    (binding [*suppress-render* false]
                      (on-change value caret)))))]
        ;; Attach the future for cancellation — unless the entry already got claimed.
        (swap! ra update ::pending-changes
          (fn [pc] (if (identical? token (:token (get pc id)))
                     (assoc-in pc [id :future] f)
                     pc))))))
  app)

(defn substitute-input-buffers
  "Returns `[tree' stale-ids]`: `tree` with each buffered `:input` node's `:value`
replaced by its buffer per the reconciliation rules above, and the ids whose buffers
turned out stale (prop caught up, or changed externally) and should be dropped.
Pure — the caller clears the stale ids from the runtime store."
  [tree buffers]
  (if (empty? buffers)
    [tree nil]
    (let [stale (volatile! [])
          walk  (fn walk [n]
                  (if-not (node? n)
                    n
                    (let [n (if (seq (::children n))
                              (update n ::children #(mapv walk %))
                              n)]
                      (if-let [{bv :value bo :based-on} (and (= :input (::tag n))
                                                          (get buffers (node-attr n :id)))]
                        (let [prop (str (node-attr n :value))]
                          (cond
                            (= prop (str bv)) (do (vswap! stale conj (node-attr n :id)) n)
                            (not= prop (str bo)) (do (vswap! stale conj (node-attr n :id)) n)
                            :else (assoc-in n [::attrs :value] bv)))
                        n))))]
      [(walk tree) (seq @stale)])))

(>defn multiline-input?
  "Returns true if `node` is an `:input` node whose attrs request multiline editing (`:multiline?
true`)."
  [node]
  [any? => boolean?]
  (boolean (and (node? node) (= :input (::tag node)) (true? (node-attr node :multiline?)))))

(>defn handle-input-key!
  "Applies key `key-event` to focused `input-node` (an `:input` node) in `app`,
mutating value and caret per the controlled-input model. Reads the node's current
`:value` attr and caret (from the runtime store, or — when the node opts in with a
`:caret` attr — from that attr), computes the edit, then calls the node's `:on-change`
handler with the new value and caret (interaction-util convention). The new caret is
written to the runtime store UNLESS the node opted into caret-in-state (has a `:caret`
attr), in which case the store is left for the node to manage.

Single-line vs multiline (`:multiline? true`):
* Single-line: an `:enter` key invokes the node's `:on-submit` handler with the current value
  (it does not edit); other keys use `apply-edit`.
* Multiline: editing uses `apply-edit-multiline` with the input's effective wrap width (from the
  runtime `::input-widths` store, falling back to the node's `:width` attr, then a large default
  so a not-yet-painted input wraps only on hard newlines). `:enter` inserts a `\\n` (it does NOT
  submit), and `:up`/`:down` move the caret by one visual line.

Returns `app`."
  [app input-node key-event]
  [any? ::node map? => any?]
  (p ::handle-input-key!
    (let [id              (node-attr input-node :id)
          ;; NOTE: when the input is buffered, `current-node-tree` already substituted the
          ;; buffer into `:value`, so `value` is the effective (echoed) value either way.
          value           (str (node-attr input-node :value))
          caret-in-state? (some? (node-attr input-node :caret))
          multiline?      (multiline-input? input-node)
          ;; per-input attr wins (an explicit 0 opts out); else the app-wide default.
          debounce-ms     (long (or (node-attr input-node :change-debounce-ms)
                                  (default-change-debounce-ms app)))
          buffered?       (pos? debounce-ms)]
      (if (and (not multiline?) (= :enter (:key key-event)))
        (do
          ;; A pending debounced :on-change must land before :on-submit so the app
          ;; submits against consistent state.
          (when buffered? (flush-pending-change! app id))
          (when-let [submit (node-attr input-node :on-submit)]
            (submit value))
          app)
        (let [caret (if caret-in-state?
                      (long (node-attr input-node :caret))
                      (get-caret app id (count value)))
              width (when multiline?
                      (input-width app id (long (or (node-attr input-node :width) 1000000))))
              {new-value :value new-caret :caret} (if multiline?
                                                    (apply-edit-multiline value caret width key-event)
                                                    (apply-edit value caret key-event))]
          (if buffered?
            (do
              ;; Echo from the buffer now; the app's :on-change fires after `debounce-ms`
              ;; of key silence (or at blur/submit). `:based-on` stays the prop value the
              ;; buffer originally diverged from so reconciliation can tell our own commit
              ;; landing apart from an external change.
              (let [based-on (or (:based-on (get-input-buffer app id)) value)]
                (set-input-buffer! app id {:value new-value :based-on based-on}))
              (when-let [on-change (node-attr input-node :on-change)]
                (schedule-pending-change! app id debounce-ms on-change new-value new-caret)))
            (when-let [on-change (node-attr input-node :on-change)]
              (on-change new-value new-caret)))
          (when-not caret-in-state?
            (set-caret! app id new-caret))
          app)))))

;; ----------------------------------------------------------------------------
;; Key routing (bubbling) + global keymap
;; ----------------------------------------------------------------------------

(>defn key-chord
  "Returns the normalized chord for key event `event`, used to look up a handler in a
global keymap. With no modifiers, a special key returns its `:key` keyword (e.g.
`:tab`) and a printable key returns its 1-char string (e.g. `\"a\"`). When a
modifier is set, returns a vector of the active modifier keywords (in
`[:ctrl :alt :shift]` order) followed by the base key, e.g. `[:ctrl \"q\"]`."
  [event]
  [map? => any?]
  (let [base (or (:key event) (:char event))
        mods (cond-> []
               (:ctrl? event) (conj :ctrl)
               (:alt? event) (conj :alt)
               (:shift? event) (conj :shift))]
    (if (seq mods)
      (conj mods base)
      base)))

(>defn- node-path
  "Returns a vector of nodes from `node-tree`'s root down to (and including) the node
whose `:id` is `target-id`, in root→target order, or `nil` when not found."
  [node-tree target-id]
  [any? any? => (? vector?)]
  (letfn [(search [x]
            (when (node? x)
              (if (= target-id (node-attr x :id))
                [x]
                (some (fn [c] (when-let [p (search c)] (into [x] p)))
                  (::children x)))))]
    (search node-tree)))

(>defn route-key
  "Routes key event `key-event` through `node-tree`, returning a truthy value when the
event was handled. Dispatch precedence:

(a) the focused node's `:on-key` handler (focused node = the one whose `:id` is
    `focus-id`), then
(b) the `:on-key` handlers of its ancestors, from nearest to root (bubbling),
stopping as soon as a handler returns a truthy value (e.g. `:handled`); then
(c) if still unhandled, the handler in `global-keymap` (a map from a normalized
    chord — see `key-chord` — to a handler) for this event's chord.

`:on-key` handlers receive the `key-event` (interaction-util convention); a global
keymap handler receives `context` and the `key-event`. Returns the truthy handler
result, or `false` when nothing handled the event."
  [context node-tree focus-id key-event global-keymap]
  [any? any? any? map? (? map?) => any?]
  (p ::route-key
    (let [path    (node-path node-tree focus-id)
          ;; nearest (focused) first, then ancestors toward root
          chain   (reverse path)
          bubbled (reduce
                    (fn [_ node]
                      (when-let [h (node-attr node :on-key)]
                        (let [r (h key-event)]
                          (when r (reduced r)))))
                    nil
                    chain)]
      (cond
        bubbled bubbled
        (and global-keymap (contains? global-keymap (key-chord key-event)))
        (let [h (get global-keymap (key-chord key-event))]
          (or (h context key-event) true))
        :else false))))

;; ----------------------------------------------------------------------------
;; Overlays (modal / picker)
;; ----------------------------------------------------------------------------

(>defn modal-node?
  "Returns true if `node` is a `:modal` overlay node."
  [node]
  [any? => boolean?]
  (and (node? node) (= :modal (::tag node))))

(>defn collect-overlays
  "Returns a vector of the OPEN `:modal` nodes in `node-tree` (those whose `:open?` attr is truthy), in
document (pre-order, depth-first) order. Closed modals are omitted. The last element is the topmost
overlay (a later sibling/descendant draws over earlier ones)."
  [node-tree]
  [any? => vector?]
  (let [out (volatile! (transient []))]
    (letfn [(walk [x]
              (when (node? x)
                (when (and (modal-node? x) (node-attr x :open?))
                  (vswap! out conj! x))
                (doseq [c (::children x)] (walk c))))]
      (walk node-tree))
    (persistent! @out)))

(>defn strip-overlays
  "Returns `node-tree` with every `:modal` node (open or closed) removed from its children, recursively.
The base layout/paint walks this stripped tree so overlays never occupy space or paint inline — they
are composited separately by the driver."
  [node-tree]
  [any? => any?]
  (if (node? node-tree)
    (update node-tree ::children
      (fn [cs]
        (into []
          (keep (fn [c]
                  (cond
                    (modal-node? c) nil
                    (node? c) (strip-overlays c)
                    :else c)))
          cs)))
    node-tree))

(>defn active-tree
  "Returns the subtree that should receive focus and keyboard input. When an overlay is open it is
the topmost (last in document order) OPEN `:modal` node — trapping focus to the overlay; otherwise it
is `node-tree` itself. In either case any other (closed or nested) `:modal` nodes are stripped, so a
closed modal's contents are never focusable and only the active layer's controls take keys."
  [node-tree]
  [any? => any?]
  (strip-overlays (or (peek (collect-overlays node-tree)) node-tree)))

(>defn collect-shortcuts
  "Returns a map of `key-chord` -> `{:id :action}` for every node in `node-tree` declaring a
`:shortcut` (a chord in `key-chord` form, e.g. `[:alt \"s\"]` or `:f2`). `:action` is the node's
`:shortcut-action`, defaulting to `:activate` for `:button` nodes and `:focus` for everything else.
On a chord collision the last node in document (pre-order) order wins.

Callers gate invocation on the terminal's enhanced-keyboard capability (`*enhanced-keys?*`): when the
protocol is inactive the shortcut layer is disabled and this is not consulted."
  [node-tree]
  [any? => map?]
  (let [out (volatile! (transient {}))]
    (letfn [(walk [x]
              (when (node? x)
                (when-let [chord (node-attr x :shortcut)]
                  (let [action (or (node-attr x :shortcut-action)
                                 (if (= :button (::tag x)) :activate :focus))]
                    (vswap! out assoc! chord {:id (node-attr x :id) :action action})))
                (doseq [c (::children x)] (walk c))))]
      (walk node-tree))
    (persistent! @out)))

(>defn overlay-window-rect
  "Returns the on-screen `::rect` at which open `modal-node` should be placed within `screen-rect`. The
window's `:width`/`:height` (a number or `[:fraction f]`, defaulting to the modal's intrinsic size)
are resolved against the screen and clamped to it, and the window is positioned by the modal's
`:align` (`:center` by default) on both axes."
  [modal-node screen-rect]
  [::node ::rect => ::rect]
  (let [{:keys [width height align] :or {align :center}} (::attrs modal-node)
        intr (intrinsic-size modal-node)
        w    (min (:w screen-rect) (resolve-size width (:w screen-rect) (:w intr)))
        h    (min (:h screen-rect) (resolve-size height (:h screen-rect) (:h intr)))
        x    (+ (:x screen-rect) (align-offset align (:w screen-rect) w))
        y    (+ (:y screen-rect) (align-offset align (:h screen-rect) h))]
    {:x x :y y :w w :h h}))

;; ----------------------------------------------------------------------------
;; process-key! — single-step driver
;; ----------------------------------------------------------------------------

(>def ::node-tree-cache
  "Per-frame memo of the rendered node tree: `{:state <state-map> :tree <full-tree>}`, stored in the
   app runtime atom. The tree is a pure function of the state-map (focus lives in it under `::focus`),
   so the state-map's IDENTITY is a complete cache key. The driver's `render!` always renders fresh
   (it is the painting authority) and writes this entry; `current-node-tree` reuses it when the
   state-map is unchanged — which is the common case between a paint and the next keystroke — so
   focus-ring computation in `process-key!` does not re-render the whole tree a second time."
  (s/nilable (s/keys :req-un [::tree])))
(>def ::tree any?)

(>defn current-node-tree
  "Returns the current pure TUI node tree for `app`, computed from its state. The root
class is read from the runtime atom
(`:com.fulcrologic.fulcro.application/root-class`); its props are obtained via
`fdn/db->tree` of the root query over the state-map. `*current-focus*` is bound to
the current `::focus` while rendering so render code can call `focused?`.

The result is memoized in the runtime atom keyed on state-map IDENTITY (`::node-tree-cache`): when
the state-map has not changed since the tree was last built (by `render!` or a prior call here) the
cached tree is returned, avoiding a redundant full render-tree walk (e.g. `process-key!` resolving
the focus ring on the same state the last frame painted). Any state mutation yields a new map
identity, so the cache can never go stale.

Buffered input values (`::input-buffers`, see `:change-debounce-ms`) are substituted into
the built tree here (`substitute-input-buffers`) — this is the single seam through which
both key dispatch and painting obtain the tree, so the buffered value is what gets laid
out, painted, and edited. Buffers found stale by reconciliation are dropped from the
store, and the store's identity joins the cache key so a buffered keystroke (which
changes no app state) still yields a fresh tree."
  [app]
  [any? => any?]
  (let [state-map  (some-> app :com.fulcrologic.fulcro.application/state-atom deref)
        rt-atom    (:com.fulcrologic.fulcro.application/runtime-atom app)
        rt         (some-> rt-atom deref)
        root-class (:com.fulcrologic.fulcro.application/root-class rt)
        cache      (::node-tree-cache rt)
        ;; The tree also depends on hook state (e.g. `use-state`), which lives in the runtime atom — NOT
        ;; the state-map. A hook setter swaps the registry, so include its identity in the cache key or a
        ;; buffered input edited via `use-state` would never repaint.
        hooks-reg  (get rt ::hooks/hook-registry)
        buffers    (::input-buffers rt)]
    (cond
      (and cache
        (identical? (:state cache) state-map)
        (identical? (:hooks cache) hooks-reg)
        (identical? (:buffers cache) buffers)) (:tree cache)
      (and state-map root-class)
      (let [query     (rc/get-query root-class state-map)
            props     (fdn/db->tree query state-map state-map)
            tree      (binding [*current-focus* (get state-map ::focus)]
                        (render-root root-class props app))
            ;; render-root mounts/cleans up hooks, so re-read the registry identity for the cache key.
            hooks-reg (get (some-> rt-atom deref) ::hooks/hook-registry)
            [tree stale-ids] (substitute-input-buffers tree buffers)]
        (doseq [id stale-ids]
          ;; A stale buffer's pending :on-change is cancelled too: either it already
          ;; fired (that's how the prop caught up) or an external change superseded
          ;; the user's uncommitted edit — in both cases it must not land later.
          (cancel-pending-change! app id)
          (clear-input-buffer! app id))
        (when rt-atom
          (swap! rt-atom assoc ::node-tree-cache
            {:state   state-map
             :hooks   hooks-reg
             ;; key on the post-reconciliation store (stale ids just cleared)
             :buffers (get (deref rt-atom) ::input-buffers)
             :tree    tree}))
        tree)
      :else nil)))

(>defn- resolve-focus!
  "Re-resolves focus after a dispatch may have changed `app`'s state/tree. Recomputes
focusables from the freshly rendered `node-tree`; if the currently focused id is no
longer focusable it is moved to the next id in `focus-order` (else the first; else
`nil`), firing the appropriate `:on-lost-focus`/`:on-focus` transitions. Returns
`app`."
  [app node-tree]
  [any? any? => any?]
  (let [focs   (focusables node-tree)
        ids    (into #{} (map :id) focs)
        old-id (current-focus app)]
    (if (contains? ids old-id)
      app
      (let [order  (focus-order focs)
            new-id (or (next-focus order old-id) (first (mapv :id order)))]
        (focus! app new-id)
        (apply-focus-change! app node-tree old-id new-id)
        app))))

(>defn process-key!
  "Single-step driver: applies key event `key-event` to `app`, mutating focus and/or
state synchronously, and returns `app`.

Steps:
1. Compute the current node tree from app state (`current-node-tree`).
2. Dispatch by precedence:
   * `:tab` → focus the `next-focus` in the focus ring;
   * `:backtab` or Shift-`:tab` → focus the `prev-focus`;
   * `:down` → focus the `next-focus`; `:up` → focus the `prev-focus`
     (arrow focus navigation, mirroring `:tab`/`:backtab` in the ring);
     (all of the above then `focus!` + fire `apply-focus-change!`)
   * else if the focused node is an `:input` → controlled-input editing
     (`handle-input-key!`);
   * else → `route-key` (focused `:on-key` → bubble to ancestors → global keymap).
3. After dispatch, re-resolve focus against the (possibly new) node tree: if the
   focused id vanished, advance to the next focusable (else first; else nil),
   firing transitions.

Arrow-key capture rule: `:up`/`:down` move focus EXCEPT when the focused node is an
`:input` whose attrs set `:multiline? true` — such an input *captures* `:up`/`:down`,
routing them to `handle-input-key!` (reserved for future multiline caret movement)
rather than navigating focus. A single-line `:input` (no `:multiline?`) does NOT
capture them, so `:up`/`:down` navigate focus while it uses only left/right/home/end
for the caret.

`global-keymap` (optional) maps normalized chords (see `key-chord`) to handlers
invoked as `(handler app key-event)`. Works on a synchronous raw app with NO
terminal attached.

TODO: viewport scrolling / follow-focus (keeping the focused node's placed rect
visible) is intentionally NOT implemented here — it requires placed rects and the
terminal size and is handled by a later task."
  ([app key-event]
   [any? map? => any?]
   (process-key! app key-event nil))
  ([app key-event global-keymap]
   [any? map? (? map?) => any?]
   (p ::process-key!
     (let [;; When an overlay is open, focus and keyboard input are trapped to its subtree (the
           ;; base UI is inert behind it). `active-tree` is that overlay, or the full tree otherwise.
           node-tree        (active-tree (current-node-tree app))
           overlay?         (modal-node? node-tree)
           k                (:key key-event)
           shift?           (:shift? key-event)
           old-id           (current-focus app)
           order            (focus-order (focusables node-tree))
           focused-node     (when (some? old-id) (find-by-id node-tree old-id))
           multiline-input? (and focused-node
                              (= :input (::tag focused-node))
                              (true? (node-attr focused-node :multiline?)))
           nav-down?        (and (= k :down) (not multiline-input?))
           nav-up?          (and (= k :up) (not multiline-input?))
           ;; Control shortcuts are gated on the enhanced-keyboard protocol and only ever bind
           ;; modified/function chords, so they can be matched at high precedence (even while an
           ;; input is focused) without conflicting with typing or focus navigation.
           shortcut         (when *enhanced-keys?*
                              (get (collect-shortcuts node-tree) (key-chord key-event)))]
       (cond
         ;; Escape dismisses the active overlay via its (application-supplied) :on-dismiss handler.
         (and overlay? (= k :escape) (node-attr node-tree :on-dismiss))
         ((node-attr node-tree :on-dismiss))

         ;; A declared control shortcut focuses its target (firing transitions) and, when its action
         ;; is :activate, fires the target's :on-activate ("click"). Reserved app `:global-keymap`
         ;; chords are intercepted by the input loop before process-key! runs, so they win.
         shortcut
         (let [{:keys [id action]} shortcut]
           (focus! app id)
           (apply-focus-change! app node-tree old-id id)
           (when (= action :activate)
             (some-> (find-by-id node-tree id) activate!)))

         (or (= k :backtab) (and (= k :tab) shift?) nav-up?)
         (let [new-id (prev-focus order old-id)]
           (focus! app new-id)
           (apply-focus-change! app node-tree old-id new-id))

         (or (= k :tab) nav-down?)
         (let [new-id (next-focus order old-id)]
           (focus! app new-id)
           (apply-focus-change! app node-tree old-id new-id))

         :else
         (let [;; Alt/Ctrl-modified chords are never plain text, so a focused input must NOT
               ;; consume them; they fall through to `route-key` so an ancestor `:on-key` (e.g. a
               ;; subform's item-to-item navigation) or the global keymap can handle them even while
               ;; a field is being edited. Shift alone is ordinary uppercase typing and is captured.
               modified? (or (:ctrl? key-event) (:alt? key-event))]
           (cond
             (and focused-node (= :input (::tag focused-node)) (not modified?))
             (handle-input-key! app focused-node key-event)

             ;; Enter or Space on a focusable that has an :on-activate handler activates it.
             (and focused-node
               (node-attr focused-node :on-activate)
               (or (= k :enter) (= (:char key-event) " ")))
             (activate! focused-node)

             :else
             (route-key app node-tree old-id key-event global-keymap))))
       ;; re-resolve focus against the post-dispatch active tree (the overlay if one is open, else the
       ;; full tree). When a modal opens this draws focus into it; when it closes, focus returns to base.
       (resolve-focus! app (active-tree (current-node-tree app)))
       app))))
