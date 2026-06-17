(ns com.fulcrologic.fulcro.tui.terminal
  "A self-contained terminal abstraction for a TUI rendering target.

   This namespace OWNS the normalized key-event model that downstream TUI code consumes, a pure
   (JLine-free) key decoder, a `Terminal` protocol, a real JLine-backed implementation, and an
   atom-backed fake (`string-terminal`) used for tests.

   This is JVM/babashka only (plain `.clj`)."
  (:require
    [clojure.spec.alpha :as s]
    [com.fulcrologic.fulcro.tui.perf :as perf :refer [p]]
    [com.fulcrologic.guardrails.core :refer [=> >def >defn >defn- ?]])
  (:import
    (org.jline.terminal  TerminalBuilder)
    (org.jline.utils NonBlockingReader)
    (sun.misc Signal SignalHandler)))

;; =============================================================================
;; Normalized key-event model
;; =============================================================================

(def special-keys
  "The set of keyword values allowed as a special-key `:key`."
  #{:enter :tab :backtab :escape :backspace :delete
    :up :down :left :right
    :home :end :page-up :page-down})

(defn single-codepoint-string?
  "Returns true if `s` is a string consisting of exactly one unicode code point. Note that an
   astral/supplementary code point occupies two UTF-16 chars yet is still a single code point, so
   this counts code points rather than `count` (which counts UTF-16 code units)."
  [s]
  (and (string? s)
    (pos? (count s))
    (= 1 (.codePointCount ^String s 0 (count s)))))

(>def ::key (s/or :special special-keys
              :printable single-codepoint-string?))
(>def ::char (s/nilable string?))
(>def ::ctrl? boolean?)
(>def ::alt? boolean?)
(>def ::shift? boolean?)
(>def ::raw (s/or :code-point int? :code-points (s/coll-of int? :kind vector?)))

(>def ::key-event
  (s/keys :req-un [::key ::ctrl? ::alt? ::shift?]
    :opt-un [::char ::raw]))

(>defn key-event
  "Returns a normalized key event map. `key` is a 1-char string (printable) or a keyword from
`special-keys`. The remaining values default to a non-modified, non-char event; pass `opts`
(a map of any of `:char :ctrl? :alt? :shift? :raw`) to override."
  ([key]
   [::key => ::key-event]
   (key-event key {}))
  ([key opts]
   [::key map? => ::key-event]
   (merge {:key    key
           :char   nil
           :ctrl?  false
           :alt?   false
           :shift? false}
     opts)))

;; =============================================================================
;; Pure key decoder (testable WITHOUT JLine)
;; =============================================================================

(def ^:private cp->special-key
  "Control code points that must decode to a keyword key (not their literal text char), shared by the
   raw decoder and the CSI-u decoder so modified forms (e.g. Shift-Tab as `9;2u`) yield `:tab`."
  {9 :tab, 13 :enter, 10 :enter, 27 :escape, 8 :backspace, 127 :backspace})

(>defn- ctrl-letter
  "Returns the lowercase letter string for a control code `n` in 1..26 (1 -> \"a\" .. 26 -> \"z\")."
  [n]
  [int? => string?]
  (str (char (+ (int \a) (dec n)))))

(>defn- printable-event
  "Returns a printable `::key-event` for the unicode code point `cp` (the `:key` and `:char` are the
1-char string for `cp`)."
  [cp]
  [int? => ::key-event]
  (let [s (String. (Character/toChars cp))]
    (key-event s {:char s :raw cp})))

(>defn- csi-event
  "Returns `[event remaining]` for a CSI (ESC `[`) sequence, given `rest-ints` (the ints AFTER the
leading `27 91`). Returns nil if the sequence is not recognized so the caller can fall back."
  [rest-ints]
  [(s/coll-of int?) => (? (s/tuple ::key-event (s/coll-of int?)))]
  (let [v     (vec rest-ints)
        f     (first v)
        raw-2 (fn [k]                                       ; two-byte CSI like 27 91 65 ("A")
                [(key-event k {:raw [27 91 f]}) (subvec v 1)])
        raw-3 (fn [k]                                       ; three-byte CSI like 27 91 51 126 ("3~")
                [(key-event k {:raw [27 91 f 126]}) (subvec v 2)])]
    (cond
      (= f 65) (raw-2 :up)
      (= f 66) (raw-2 :down)
      (= f 67) (raw-2 :right)
      (= f 68) (raw-2 :left)
      (= f 72) (raw-2 :home)
      (= f 70) (raw-2 :end)
      (= f 90) (raw-2 :backtab)                             ; ESC [ Z = Shift-Tab
      ;; numeric forms terminated by ~ (126)
      (and (= (second v) 126))
      (case (int f)
        51 (raw-3 :delete)                                  ; 3~
        49 (raw-3 :home)                                    ; 1~
        52 (raw-3 :end)                                     ; 4~
        53 (raw-3 :page-up)                                 ; 5~
        54 (raw-3 :page-down)                               ; 6~
        nil)
      :else nil)))

(>defn- read-decimal
  "Returns `[n remaining]` for the leading run of ASCII decimal digits in `v` (a vector of ints), or
nil when `v` does not start with a digit."
  [v]
  [vector? => (? (s/tuple int? vector?))]
  (when (and (seq v) (<= 48 (int (first v)) 57))
    (loop [n 0 v v]
      (if (and (seq v) (<= 48 (int (first v)) 57))
        (recur (+ (* n 10) (- (int (first v)) 48)) (subvec v 1))
        [n v]))))

(>defn- csi-u-event
  "Returns `[event remaining]` for a Kitty/fixterms CSI-u key sequence, given `rest-ints` (the ints
AFTER the leading `27 91`). The form is `<codepoint> [; <modifiers>] u` (final byte `u` = 117). The
modifier field is `1 + bitmask` where bit 0 = shift, bit 1 = alt, bit 2 = ctrl. Returns nil when the
sequence is not a well-formed CSI-u sequence, so the caller can fall back to `csi-event`.

`:char` is populated only for unmodified or shift-only keys (actual text); ctrl/alt combos carry a
nil `:char`, matching the legacy control-code decoding."
  [rest-ints]
  [(s/coll-of int?) => (? (s/tuple ::key-event (s/coll-of int?)))]
  (let [v (vec rest-ints)]
    (when-let [[cp after-cp] (read-decimal v)]
      (let [[mods after-mods] (if (= (some-> (first after-cp) int) 59) ; ';'
                                (or (read-decimal (subvec after-cp 1)) [nil after-cp])
                                [1 after-cp])]
        (when (and mods (seq after-mods) (= (int (first after-mods)) 117)) ; 'u'
          (let [bits     (dec mods)
                ctrl?    (pos? (bit-and bits 4))
                alt?     (pos? (bit-and bits 2))
                shift?   (pos? (bit-and bits 1))
                ;; Control codepoints (tab/enter/escape/backspace) must decode to their KEYWORD key
                ;; (e.g. :tab), exactly as `decode-key` does for the raw bytes — otherwise modified
                ;; forms like Shift-Tab (`9;2u`) would arrive as the string "\t" and miss the
                ;; engine's `(= k :tab)` focus-nav check. Other codepoints stay as their text string.
                special  (get cp->special-key cp)
                s        (String. (Character/toChars cp))
                k        (or special s)]
            [(key-event k {:char   (when (and (not special) (not (or ctrl? alt?))) s)
                           :ctrl?  ctrl?
                           :alt?   alt?
                           :shift? shift?
                           :raw    (into [27 91] v)})
             (subvec after-mods 1)]))))))

(>defn decode-key
  "Decodes the next key from a sequence of input code points `ints`.

Returns `[event remaining-ints]`, consuming exactly the code points for one key, or `nil` when
`ints` is empty. The decoder is pure and contains no JLine/IO dependency. Handles:

* printable ASCII / multi-byte unicode code points -> printable event
* 9 -> `:tab`; 10 or 13 -> `:enter`; 8 or 127 -> `:backspace`
* 27 alone (nothing following) -> `:escape`
* CSI-u sequences (`27 91 <cp> [; <mods>] u`) -> modified keys with `:ctrl?/:alt?/:shift?`
  (Kitty/fixterms enhanced keyboard protocol)
* CSI cursor/edit sequences (`27 91 ...`) -> arrows, home/end, delete, page-up/down
* control combos 1..26 -> `{:ctrl? true :key \"a\"..\"z\"}` (tab/enter handled first)"
  [ints]
  [(s/coll-of int?) => (? (s/tuple ::key-event (s/coll-of int?)))]
  (let [v (vec ints)]
    (when (seq v)
      (let [c    (int (first v))
            rest (subvec v 1)]
        (cond
          (= c 9) [(key-event :tab {:raw c}) rest]
          (or (= c 10) (= c 13)) [(key-event :enter {:raw c}) rest]
          (or (= c 8) (= c 127)) [(key-event :backspace {:raw c}) rest]
          (= c 27)
          (cond
            (empty? rest) [(key-event :escape {:raw c}) rest]
            (= (int (first rest)) 91)
            (or (csi-u-event (subvec v 2))
              (csi-event (subvec v 2))
              ;; unrecognized CSI: treat ESC as escape, leave the rest
              [(key-event :escape {:raw c}) rest])
            ;; ESC + something else: treat ESC as escape (alt-combos not modeled here)
            :else [(key-event :escape {:raw c}) rest])
          ;; control combos 1..26 (9/13 already handled above)
          (and (>= c 1) (<= c 26))
          [(key-event (ctrl-letter c) {:ctrl? true :raw c}) rest]
          ;; printable / multi-byte unicode
          (>= c 32) [(printable-event c) rest]
          ;; anything else (e.g. 0): consume as printable code point best-effort
          :else [(printable-event c) rest])))))

;; =============================================================================
;; Terminal protocol
;; =============================================================================

(defprotocol Terminal
  "Abstraction over a terminal device. Coordinates are 0-based (`x` column, `y` row)."
  (t-size [t] "Returns `{:rows R :cols C}`.")
  (t-read-key [t] "Returns the next normalized key event (blocking for real terminals), or nil on EOF/empty.")
  (t-write! [t s] "Writes string `s` to the terminal (no flush).")
  (t-flush! [t] "Flushes buffered output.")
  (t-set-cursor! [t x y visible?] "Positions the hardware cursor at 0-based (`x`,`y`) and shows/hides it.")
  (t-enter! [t] "Enters raw mode + alternate screen, disables auto-wrap, and hides the cursor.")
  (t-leave! [t] "Restores: shows cursor, re-enables auto-wrap, leaves alt screen, exits raw mode, closes.")
  (t-sync-supported? [t] "Returns true if synchronized output (DEC 2026 / terminfo Sync) is available.")
  (t-enhanced-keys? [t]
    "Returns true if the enhanced (Kitty/fixterms CSI-u) keyboard protocol was detected and enabled
     for this terminal (so modified keys arrive reliably as CSI-u sequences). False otherwise; the
     keyboard-shortcut layer is gated on this.")
  (t-on-resize! [t handler]
    "Registers zero-arg `handler` to be invoked when the terminal's size changes (e.g. SIGWINCH on a
     real terminal). At most one handler is kept; registering again replaces it. `nil` clears it."))

;; ANSI control strings
(def ^:private ansi-alt-screen-enter "[?1049h")
(def ^:private ansi-alt-screen-leave "[?1049l")
(def ^:private ansi-cursor-hide "[?25l")
(def ^:private ansi-cursor-show "[?25h")
;; DECAWM (auto-wrap). Disabled while the full-screen UI is up so a line momentarily wider than the
;; terminal — e.g. a frame still painted at the OLD width during a horizontal shrink, before the resize
;; re-render catches up — CLIPS at the right margin instead of wrapping its tail onto the next line
;; (which briefly shoves the frame's top-right border + the rows below it down one line). Restored on leave.
(def ^:private ansi-autowrap-disable "[?7l")
(def ^:private ansi-autowrap-enable "[?7h")
;; Kitty/fixterms enhanced keyboard protocol (https://sw.kovidgoyal.net/kitty/keyboard-protocol/).
(def ^:private ansi-kitty-query "[?u")               ; query current flags; conforming terms reply ESC [ ? <flags> u
(def ^:private ansi-kitty-enable "[>1u")             ; push flags: 1 = disambiguate escape codes (modified keys as CSI-u)
(def ^:private ansi-kitty-disable "[<1u")            ; pop one flags entry

(>defn screen-enter-ansi
  "Returns the ANSI control string that switches the terminal INTO the full-screen UI: the alternate
screen buffer, auto-wrap OFF, then the hardware cursor hidden. Auto-wrap is disabled so a line that is
momentarily wider than the terminal — e.g. a frame still painted at the old width during a horizontal
shrink, before the resize re-render catches up — clips at the right margin instead of wrapping its tail
onto the next line. The enhanced-keyboard probe (which reads a reply) is the caller's concern, not part
of this pure prefix."
  []
  [=> string?]
  (str ansi-alt-screen-enter ansi-autowrap-disable ansi-cursor-hide))

(>defn screen-leave-ansi
  "Returns the ANSI control string that restores the terminal on exit — the inverse of
`screen-enter-ansi`: pop the pushed enhanced-keyboard flags (only when `enhanced?`), show the cursor,
re-enable auto-wrap, then leave the alternate screen."
  [enhanced?]
  [any? => string?]
  (str (when enhanced? ansi-kitty-disable) ansi-cursor-show ansi-autowrap-enable ansi-alt-screen-leave))

(>defn cursor-position-string
  "Returns the ANSI escape sequence that moves the cursor to 0-based (`x`,`y`). ANSI is 1-based, so
both are incremented."
  [x y]
  [int? int? => string?]
  (str "[" (inc y) ";" (inc x) "H"))

;; =============================================================================
;; JLine implementation
;; =============================================================================

(defn- read-key-from-reader
  "Reads the next normalized key from a JLine `NonBlockingReader`. Reads one code point (blocking);
   if it is ESC, peeks (with a short timeout) for a following CSI sequence to disambiguate a bare
   ESC from arrow/edit keys, accumulating available ints and running them through `decode-key`.
   Returns nil on EOF."
  [^NonBlockingReader reader]
  (let [c (.read reader)]
    (cond
      (= c NonBlockingReader/EOF) nil
      (= c 27)
      ;; gather any immediately-available following bytes for CSI disambiguation
      (let [acc (transient [27])]
        (loop []
          (let [n (.read reader 5)]                         ; 5ms peek window
            (when (and (not= n NonBlockingReader/READ_EXPIRED)
                    (not= n NonBlockingReader/EOF))
              (conj! acc (int n))
              (recur))))
        (let [ints (persistent! acc)
              [ev _] (decode-key ints)]
          ev))
      :else
      (let [[ev _] (decode-key [c])]
        ev))))

(defn- kbd-debug!
  "Appends a one-line diagnostic `msg` to the keyboard-negotiation debug log, but only when the
   `fulcro.tui.kbd-debug` system property (or `FULCRO_TUI_KBD_DEBUG` env var) is set. The log path is
   that value when it looks like a path, else `/tmp/fulcro-tui-kbd.log`. Startup-only, so it is cheap
   and never runs in the hot path; a write failure is swallowed."
  [msg]
  (when-let [flag (or (System/getProperty "fulcro.tui.kbd-debug")
                    (System/getenv "FULCRO_TUI_KBD_DEBUG"))]
    (try
      (let [path (if (re-find #"[/.]" (str flag)) (str flag) "/tmp/fulcro-tui-kbd.log")]
        (spit path (str msg \newline) :append true))
      (catch Throwable _ nil))))

(defn- read-csi-u-reply
  "Reads a CSI-u-style reply from `r` after the query was written: blocks up to `first-timeout` ms for
   the first byte, then accumulates following bytes (each within `tail-timeout` ms) until the `u`
   terminator (117), EOF, or a timeout. Returns the reply as a vector of ints (empty if nothing
   arrived). Consumes only the reply so it never leaks into the input loop."
  [^NonBlockingReader r first-timeout tail-timeout]
  (let [first-c (.read r (long first-timeout))]
    (if (or (= first-c NonBlockingReader/READ_EXPIRED) (= first-c NonBlockingReader/EOF))
      []
      (loop [acc (transient [(int first-c)])]
        (let [n (.read r (long tail-timeout))]
          (cond
            (= (int n) 117)                                 ; 'u' terminates the reply
            (persistent! (conj! acc 117))
            (or (= n NonBlockingReader/READ_EXPIRED) (= n NonBlockingReader/EOF))
            (persistent! acc)
            :else
            (recur (conj! acc (int n)))))))))

(defn- enhanced-keys-override
  "Returns `:force`, `:off`, or nil from the `fulcro.tui.enhanced-keys` system property (or
   `FULCRO_TUI_ENHANCED_KEYS` env var). `force`/`on`/`true`/`1` ⇒ `:force` (skip auto-detection and
   enable the protocol — for terminal stacks that carry CSI-u but do NOT answer the query, e.g. tmux
   with `extended-keys on`). `off`/`false`/`0` ⇒ `:off` (force-disable). Anything else ⇒ nil (probe)."
  []
  (when-let [v (some-> (or (System/getProperty "fulcro.tui.enhanced-keys")
                         (System/getenv "FULCRO_TUI_ENHANCED_KEYS"))
                 str
                 (.trim)
                 (.toLowerCase))]
    (cond
      (#{"force" "on" "true" "1" "yes"} v) :force
      (#{"off" "false" "0" "no"} v)        :off
      :else                                nil)))

(defn- negotiate-enhanced-keys!
  "Probes for the Kitty/fixterms enhanced keyboard protocol on the JLine `term` (already in raw mode)
   and enables it when present. Writes the query, then reads any reply: a conforming terminal answers
   with `ESC [ ? <flags> u`, while others stay silent (read times out). On a positive reply, pushes
   the enable flags and returns true; otherwise returns false. The reply bytes are consumed here so
   they never leak into the input loop.

   The `fulcro.tui.enhanced-keys` system property / `FULCRO_TUI_ENHANCED_KEYS` env var overrides the
   probe: `force` enables the protocol without querying (push the flags and trust it — needed under
   tmux/screen, which carry CSI-u once configured but swallow the query); `off` force-disables it.

   Set the `fulcro.tui.kbd-debug` system property (or `FULCRO_TUI_KBD_DEBUG` env var) to log the raw
   query/reply bytes to a file (see `kbd-debug!`) when diagnosing terminals that report OFF."
  [^org.jline.terminal.Terminal term]
  (try
    (let [override (enhanced-keys-override)
          w        (.writer term)
          r        ^NonBlockingReader (.reader term)]
      (case override
        :off (do (kbd-debug! "[fulcro-tui kbd] override=off → disabled") false)
        :force (do
                 (.write w ^String ansi-kitty-enable)
                 (.flush w)
                 (kbd-debug! "[fulcro-tui kbd] override=force → flags pushed, enabled (no probe)")
                 true)
        (do
          (.write w ^String ansi-kitty-query)
          (.flush w)
          ;; 250ms first-byte window (generous for slow/remote terminals; startup-only so latency is
          ;; irrelevant), then 30ms between the few reply bytes.
          (let [reply (read-csi-u-reply r 250 30)
                ok?   (and (= (take 3 reply) [27 91 63])    ; ESC [ ?
                        (= (peek reply) 117))]
            (kbd-debug! (str "[fulcro-tui kbd] query=" (mapv int ansi-kitty-query)
                          " reply-bytes=" reply
                          " reply-str=" (pr-str (apply str (map char reply)))
                          " enhanced?=" (boolean ok?)))
            (when ok?
              (.write w ^String ansi-kitty-enable)
              (.flush w))
            (boolean ok?)))))
    (catch Throwable t
      (kbd-debug! (str "[fulcro-tui kbd] negotiation threw: " (ex-message t)))
      false)))

(deftype JLineTerminal [^org.jline.terminal.Terminal term resize-handler closed? enhanced?]
  Terminal
  (t-size [_]
    {:rows (.getHeight term) :cols (.getWidth term)})
  (t-read-key [_]
    (p :io/read-key (read-key-from-reader (.reader term))))
  (t-write! [_ s]
    (p :io/write (.write (.writer term) ^String s)))
  (t-flush! [_]
    (p :io/flush (.flush (.writer term))))
  (t-set-cursor! [this x y visible?]
    (p :io/set-cursor
      (t-write! this (cursor-position-string x y))
      (t-write! this (if visible? ansi-cursor-show ansi-cursor-hide))))
  (t-enter! [this]
    (.enterRawMode term)
    (t-write! this (screen-enter-ansi))
    (t-flush! this)
    ;; Probe + enable the enhanced keyboard protocol (raw mode is required so the reply is not
    ;; line-buffered or echoed). Must run before the input loop starts so the reply is consumed here.
    (reset! enhanced? (negotiate-enhanced-keys! term)))
  (t-leave! [this]
    ;; Idempotent: `quit!` and the input loop's `finally` both call `t-leave!`, and on Ctrl-Q they
    ;; race on the same terminal. The first call restores the screen and closes the JLine terminal;
    ;; a second call must NOT touch it (writing to a closed terminal throws
    ;; `IllegalStateException: Terminal has been closed`). The CAS ensures only the first runs.
    (when (compare-and-set! closed? false true)
      (t-write! this (screen-leave-ansi @enhanced?))
      (t-flush! this)
      (.close term)))
  (t-sync-supported? [_]
    ;; best-effort: this JLine/terminfo build has no Sync capability enum, so report false.
    false)
  (t-enhanced-keys? [_] (boolean @enhanced?))
  (t-on-resize! [_ handler]
    (reset! resize-handler handler)
    ;; Deliver terminal-resize (SIGWINCH) to the registered handler. We use `sun.misc.Signal`
    ;; instead of JLine's `(.handle term Terminal$Signal/WINCH ...)` because JLine's signal enum
    ;; and `SignalHandler` are INNER classes that babashka's SCI can neither resolve symbolically
    ;; nor `reify`. `sun.misc.Signal`/`SignalHandler` are top-level, so the SAME code runs on the
    ;; JVM and under bb. Installing here (after the terminal is built) also overrides the WINCH
    ;; handler JLine installs for itself. JLine/the OS deliver this on a separate signal thread, so
    ;; the handler must be safe to call concurrently with the input loop. Wrapped in try/catch:
    ;; WINCH is absent on some platforms (e.g. Windows), where resize signals are simply ignored.
    (try
      (Signal/handle
        (Signal. "WINCH")
        (reify SignalHandler
          (handle [_ _sig]
            (when-let [h @resize-handler] (h)))))
      (catch Throwable _ nil))
    nil))

(defn jline-terminal
  "Returns a `Terminal` backed by a system JLine terminal (`TerminalBuilder`)."
  []
  (let [term (.. (TerminalBuilder/builder) (system true) (build))]
    (->JLineTerminal term (atom nil) (atom false) (atom false))))

(defn probe-enhanced-keys!
  "Diagnostic: builds a system JLine terminal, sends the Kitty/CSI-u progressive-enhancement query,
   reads whatever the terminal replies (no alt-screen, no shortcut handling), restores the terminal,
   and PRINTS the raw reply bytes and the OK/not-OK verdict to stdout. Run this directly in the
   terminal you want to test (e.g. `clojure -e \"((requiring-resolve 'com.fulcrologic.fulcro.tui.terminal/probe-enhanced-keys!))\"`).
   A conforming terminal replies `ESC [ ? <flags> u` (bytes start `27 91 63`, end `117`)."
  []
  (let [term (.. (TerminalBuilder/builder) (system true) (build))]
    (try
      (.enterRawMode term)
      (let [w (.writer term)
            r ^NonBlockingReader (.reader term)]
        (.write w ^String ansi-kitty-query)
        (.flush w)
        (let [reply (read-csi-u-reply r 500 40)
              ok?   (and (= (take 3 reply) [27 91 63]) (= (peek reply) 117))]
          (.close term)
          (println)
          (println "=== fulcro-tui enhanced-keyboard probe ===")
          (println "TERM         =" (System/getenv "TERM"))
          (println "TERM_PROGRAM =" (System/getenv "TERM_PROGRAM"))
          (println "query bytes  =" (mapv int ansi-kitty-query) " (ESC [ ? u)")
          (println "reply bytes  =" reply)
          (println "reply string =" (pr-str (apply str (map char reply))))
          (println "enhanced?    =" ok?)
          (when-not ok?
            (println)
            (if (empty? reply)
              (println "No reply: this terminal did not answer the query — the Kitty keyboard protocol")
              (println "Unexpected reply shape — the terminal answered but not with ESC [ ? <flags> u."))
            (println "is either unsupported or disabled. Shortcuts/mnemonics stay OFF here."))
          ok?))
      (catch Throwable t
        (try (.close term) (catch Throwable _ nil))
        (println "probe threw:" (ex-message t))
        false))))

(defn probe-key!
  "Diagnostic: builds a system JLine terminal, ENABLES the enhanced keyboard protocol (same push the
   driver does), then reads `n` (default 8) keypresses and prints, for each, the raw code points and
   the `decode-key` result. Use this to see what a terminal actually sends for a chord like Alt-s
   AFTER the protocol is enabled — a Kitty-conforming terminal sends `ESC [ <cp> ; <mods> u`; iTerm
   with Left-Option set to compose sends a single composed code point and NO `:alt?`.

   Run directly in the target terminal, press the keys to test, then press `q`:
   `clojure -e \"((requiring-resolve 'com.fulcrologic.fulcro.tui.terminal/probe-key!))\"`"
  ([] (probe-key! 8))
  ([n]
   (let [term (.. (TerminalBuilder/builder) (system true) (build))]
     (try
       (.enterRawMode term)
       (let [w (.writer term)
             r ^NonBlockingReader (.reader term)]
         (.write w ^String ansi-kitty-enable)
         (.flush w)
         (println "=== fulcro-tui key probe (protocol enabled) — press keys, 'q' to quit ===")
         (loop [i 0]
           (when (< i n)
             ;; gather ESC + immediately-available bytes (same heuristic as the real input loop)
             (let [first-c (.read r)]
               (when-not (= first-c NonBlockingReader/EOF)
                 (let [acc (transient [(int first-c)])]
                   (when (= first-c 27)
                     (loop []
                       (let [b (.read r 5)]
                         (when (and (not= b NonBlockingReader/READ_EXPIRED)
                                 (not= b NonBlockingReader/EOF))
                           (conj! acc (int b))
                           (recur)))))
                   (let [ints (persistent! acc)
                         [ev _] (decode-key ints)]
                     (println "raw=" ints " decoded=" (pr-str ev))
                     (when-not (= (:char ev) "q")
                       (recur (inc i)))))))))
         (.write w ^String ansi-kitty-disable)
         (.flush w)
         (.close term)
         nil)
       (catch Throwable t
         (try (.close term) (catch Throwable _ nil))
         (println "probe threw:" (ex-message t))
         nil)))))

;; =============================================================================
;; Fake terminal (string-terminal)
;; =============================================================================

(deftype StringTerminal [state]
  Terminal
  (t-size [_]
    (select-keys @state [:rows :cols]))
  (t-read-key [_]
    (let [k (-> @state :keys first)]
      (when k (swap! state update :keys (comp vec rest)))
      k))
  (t-write! [_ s]
    (swap! state update :output str s)
    nil)
  (t-flush! [_] nil)
  (t-set-cursor! [_ x y visible?]
    (swap! state assoc :cursor {:x x :y y :visible? visible?})
    nil)
  (t-enter! [_]
    (swap! state assoc :entered? true)
    nil)
  (t-leave! [_]
    (swap! state assoc :left? true)
    nil)
  (t-sync-supported? [_]
    (boolean (:sync? @state)))
  (t-enhanced-keys? [_]
    (boolean (:enhanced-keys? @state)))
  (t-on-resize! [_ handler]
    (swap! state assoc :on-resize handler)
    nil))

(defn string-terminal
  "Returns an atom-backed fake `Terminal` for testing. `opts`:

   * `:rows` - terminal height (default 24)
   * `:cols` - terminal width (default 80)
   * `:keys` - a seq of scripted `::key-event`s that `t-read-key` will dequeue, in order
   * `:sync?` - the boolean reported by `t-sync-supported?` (default false)
   * `:enhanced-keys?` - the boolean reported by `t-enhanced-keys?` (default false)

   Use the accessors `output`, `cursor`, `feed!`, and `resize!` to drive/inspect it."
  [{:keys [rows cols keys sync? enhanced-keys?] :or {rows 24 cols 80 keys []}}]
  (->StringTerminal (atom {:rows   rows :cols cols :keys (vec keys)
                           :output "" :cursor nil :sync? (boolean sync?)
                           :enhanced-keys? (boolean enhanced-keys?)})))

(defn output
  "Returns the accumulated string written to the fake terminal `t`."
  [^StringTerminal t]
  (:output @(.-state t)))

(defn cursor
  "Returns the last recorded cursor map `{:x :y :visible?}` for the fake terminal `t`, or nil."
  [^StringTerminal t]
  (:cursor @(.-state t)))

(defn feed!
  "Enqueues additional scripted key `events` onto the fake terminal `t`'s read queue."
  [^StringTerminal t & events]
  (swap! (.-state t) update :keys into events)
  nil)

(defn resize!
  "Sets the fake terminal `t` dimensions to `rows` x `cols`, then invokes its registered resize handler
   (see `t-on-resize!`), if any — simulating a real terminal's SIGWINCH delivery."
  [^StringTerminal t rows cols]
  (swap! (.-state t) assoc :rows rows :cols cols)
  (when-let [h (:on-resize @(.-state t))] (h))
  nil)
