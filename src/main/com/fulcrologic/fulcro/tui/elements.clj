(ns com.fulcrologic.fulcro.tui.elements
  "The public TUI element API: the generators authors use to build a tree of terminal-native *nodes*
   from a Fulcro component's render — `vbox`, `hbox`, `box`, `text`, `input`, `button`, `line`,
   `viewport`, `modal`, `picker` — plus `focused?` (highlight the focused node). State changes use
   Fulcro's own `com.fulcrologic.fulcro.components/transact!`; this namespace adds no transact.

   A node is a plain map keyed by the `com.fulcrologic.fulcro.tui.engine` vocabulary (`::engine/tag`,
   `::engine/attrs`, `::engine/children`); prefer these generators over building the maps by hand.
   The engine (`com.fulcrologic.fulcro.tui.engine`) lays the tree out and paints it; this namespace
   depends on the engine for that node vocabulary and `node?`/`*current-focus*`.

   This is JVM/babashka only (plain `.clj`)."
  (:require
    [com.fulcrologic.fulcro.tui.engine :as engine]
    [com.fulcrologic.guardrails.core :refer [=> >defn >defn- ?]]))

(>defn focused?
  "Returns true if `id` is the id of the node that currently has focus (per the
dynamically bound `engine/*current-focus*`)."
  [id]
  [any? => boolean?]
  (= id engine/*current-focus*))

(>defn- flatten-children
  "Returns a vector of `children` with nested sequential collections flattened and `nil`s removed.
Nodes, strings, and numbers are retained as-is, in order. This lets callers splice seqs of
children (e.g. from `map`) directly into an element's argument list."
  [children]
  [sequential? => ::engine/children]
  (persistent!
    (reduce
      (fn [acc c]
        (cond
          (nil? c) acc
          (and (sequential? c) (not (engine/node? c))) (reduce conj! acc (flatten-children c))
          :else (conj! acc c)))
      (transient [])
      children)))

(>defn element
  "Returns a TUI node with the given `tag` built from `args`. If the first of `args` is a map it is
used as the node's attributes (otherwise attributes default to `{}`); the remaining `args` become
the node's children (flattened, with `nil`s removed). Prefer the named generators (`vbox`, etc.)
over calling this directly."
  [tag args]
  [::engine/tag (? sequential?) => ::engine/node]
  (let [args (or args [])
        [attrs children] (if (map? (first args))
                           [(first args) (rest args)]
                           [{} args])]
    {::engine/tag tag ::engine/attrs attrs ::engine/children (flatten-children children)}))

(defn box
  "Returns a `:box` node: a single styling/padding/border container around `children`. An optional
   leading attribute map sets layout/style attributes."
  [& args]
  (element :box args))

(defn button
  "Returns a `:button` node rendering `children` as its label. An optional leading attribute map sets
   `:id`, `:on-activate`, and style attributes. It may also declare a keyboard shortcut:

   * `:shortcut` - a chord in `key-chord` form (e.g. `[:alt \"s\"]`, `:f2`, `[:ctrl \"k\"]`). When the
     enhanced keyboard protocol is active, pressing it focuses this control and (by default) fires
     `:on-activate`. The chord's base letter is underlined in the label as a mnemonic hint.
   * `:shortcut-action` - `:activate` (default for buttons) or `:focus` (focus only)."
  [& args]
  (element :button args))

(defn hbox
  "Returns an `:hbox` node that stacks `children` horizontally. An optional leading attribute map
   sets layout/style attributes for the container."
  [& args]
  (element :hbox args))

(defn input
  "Returns an `:input` leaf node from the given `attrs` map. Inputs are controlled: `:value` (and
   optionally `:caret`) come from props, and `:on-change` receives proposed edits. An input may also
   declare a `:shortcut` (see `button`); its `:shortcut-action` defaults to `:focus` (an input has no
   activation), so the shortcut jumps focus into the field.

   `:change-debounce-ms N` (N > 0) opts the input into engine-buffered editing: keystrokes
   echo immediately from a transient buffer while `:on-change` fires only after N ms of key
   silence (and is flushed at blur and before `:on-submit`). Use for inputs whose
   `:on-change` triggers expensive work (filtering, cascading renders); the data model
   lags typing by at most N ms but is consistent at every interaction boundary."
  [attrs]
  (element :input [attrs]))

(defn line
  "Returns a `:line` leaf node (a rule). An optional leading attribute map sets orientation/style."
  [& args]
  (element :line args))

(defn modal
  "Returns a `:modal` overlay node stacking `children` vertically inside a window that the driver
   floats over the rest of the UI (compositing it on top and trapping focus/keyboard input to it).
   An optional leading attribute map sets:

     * `:id`        - (recommended) identity for focus/queries.
     * `:open?`     - the overlay is active (composited + focus-trapped) only when truthy. When falsy
                      the modal renders nothing.
     * `:width`/`:height` - the window size in cells (a number, or a `[:fraction f]` of the screen);
                      defaults to the modal's intrinsic content size when omitted.
     * `:align`     - position on screen, one of `:center` (default), `:start`, `:end`.
     * `:border?`   - draw a border (default `true`).
     * `:title`     - a string painted onto the top border.
     * `:on-dismiss`- a zero-arg handler invoked when Escape is pressed while the modal is active.

   Lifecycle (toggling `:open?`, recording any selection) is the application's responsibility via its
   own state/mutations — this node owns no state."
  [& args]
  (let [[attrs children] (if (map? (first args)) [(first args) (rest args)] [{} args])]
    (element :modal (into [(merge {:border? true} attrs)] children))))

(defn text
  "Returns a `:text` node rendering its string/number `children` as text. An optional leading
   attribute map sets style attributes (e.g. `:color`, `:highlight`)."
  [& args]
  (element :text args))

(defn vbox
  "Returns a `:vbox` node that stacks `children` vertically. An optional leading attribute map sets
   layout/style attributes for the container."
  [& args]
  (element :vbox args))

(defn viewport
  "Returns a `:viewport` node: a fixed-size container whose (potentially larger) `children` scroll
   within its bounds. An optional leading attribute map sets size and `:id` (for scroll state)."
  [& args]
  (element :viewport args))

(>defn picker
  "Returns a `:modal` overlay presenting `options` as a scrollable list of selectable rows — a list
picker. Each row is a focusable button, so the focused row IS the highlighted choice: the focus
ring moves the highlight (Up/Down/Tab), the enclosing `:viewport` auto-scrolls to keep it visible
(PageUp/PageDown page it), Enter selects, and Escape cancels. State and selection handling are the
application's responsibility — this is a pure composition of existing nodes. `opts`:

* `:id`        - (required) base keyword for the modal and per-row focus ids.
* `:open?`     - the picker is shown only when truthy.
* `:title`     - optional title painted on the modal border.
* `:width`/`:height` - window size in cells (default 40 x 12).
* `:options`   - a vector of `{:value :label}` maps (`:value` a keyword/string/symbol, `:label`
                 the displayed text).
* `:on-select` - one-arg handler called with a row's `:value` when its row is activated (Enter).
* `:on-cancel` - zero-arg handler called on Escape (wired to the modal's `:on-dismiss`)."
  [{:keys [id open? title width height options on-select on-cancel]}]
  [map? => ::engine/node]
  (modal {:id         id :open? open? :title title
          :width      (or width 40) :height (or height 12)
          :on-dismiss on-cancel}
    (viewport {:id (keyword (str (name id) "-list")) :grow 1}
      (vbox {}
        (mapv (fn [{:keys [value label]}]
                (let [row-id (keyword (str (name id) "-" (name value)))]
                  (button {:id          row-id
                           :highlight   (focused? row-id)
                           :on-activate (fn [] (when on-select (on-select value)))}
                    (str label))))
          options)))))

