(ns com.fulcrologic.fulcro.tui.buffered-input-spec
  "Specs for `:change-debounce-ms` buffered inputs: immediate echo from the engine's
   value buffer, debounced `:on-change`, flush at blur/submit, and reconciliation
   against external state changes."
  (:require
    [com.fulcrologic.fulcro.components :as comp]
    [com.fulcrologic.fulcro.mutations :as m]
    [com.fulcrologic.fulcro.tui.application :as app]
    [com.fulcrologic.fulcro.tui.elements :as elements]
    [com.fulcrologic.fulcro.tui.engine :as engine]
    [com.fulcrologic.fulcro.tui.terminal :as term]
    [fulcro-spec.core :refer [=> assertions component specification]]))

(m/defmutation set-q [{:keys [v]}]
  (action [{:keys [state]}] (swap! state assoc :app/q v)))

(def submitted (atom nil))

(comp/defsc Root [this {:keys [app/q]}]
  {:query         [:app/q]
   :ident         (fn [] [:component/id ::root])
   :initial-state {:app/q ""}}
  (elements/vbox {:id "root"}
    (elements/input {:id                 :q
                     :value              q
                     :change-debounce-ms 40
                     :on-change          (fn [v _caret] (comp/transact! this [(set-q {:v v})]))
                     :on-submit          (fn [v] (reset! submitted v))})
    ;; second focusable so Tab blurs :q
    (elements/input {:id :other :value "" :on-change (fn [_ _])})
    (elements/text {} (str "q=" q))))

(defn- new-app []
  (app/application {:root-class Root :initial-state true}))

(defn- state [app]
  (deref (:com.fulcrologic.fulcro.application/state-atom app)))

(defn- settle!
  "Waits long enough for any pending debounced :on-change to fire, then repaints."
  [app]
  (Thread/sleep 200)
  (app/render! app)
  app)

(specification "buffered input (:change-debounce-ms)"
  (component "typing echoes immediately from the buffer while :on-change is debounced"
    (let [app (new-app)
          t   (term/string-terminal {:rows 6 :cols 30})]
      (app/attach! app t)                                   ; focus :q
      (app/step! app {:key "H" :char "H"})
      (app/step! app {:key "i" :char "i"})
      (assertions
        "the typed text is painted right away"
        (nth (app/screen-of app) 0) => "Hi                            "
        "the caret advanced with the echo"
        (engine/get-caret app :q 0) => 2
        "the app state has NOT yet seen the change (still debouncing)"
        (:app/q (state app)) => ""
        "the label row still shows the stale model value"
        (nth (app/screen-of app) 2) => "q=                            ")
      (settle! app)
      (assertions
        "after the debounce window the :on-change fired with the final value"
        (:app/q (state app)) => "Hi"
        "the label row caught up"
        (nth (app/screen-of app) 2) => "q=Hi                          "
        "the redundant buffer was dropped once the prop caught up"
        (engine/get-input-buffer app :q) => nil)))

  (component "blur (Tab away) flushes the pending :on-change immediately and drops the buffer"
    (let [app (new-app)
          t   (term/string-terminal {:rows 6 :cols 30})]
      (app/attach! app t)
      (app/step! app {:key "Y" :char "Y"})
      (app/step! app {:key "o" :char "o"})
      (app/step! app {:key :tab})
      (assertions
        "the model saw the buffered value synchronously at blur (no debounce wait)"
        (:app/q (state app)) => "Yo"
        "the buffer is gone (controlled semantics resume while blurred)"
        (engine/get-input-buffer app :q) => nil
        "focus moved on normally"
        (engine/current-focus app) => :other)))

  (component "Enter flushes the pending :on-change before :on-submit"
    (let [app (new-app)
          t   (term/string-terminal {:rows 6 :cols 30})]
      (reset! submitted nil)
      (app/attach! app t)
      (app/step! app {:key "g" :char "g"})
      (app/step! app {:key "o" :char "o"})
      (app/step! app {:key :enter})
      (assertions
        "the model was flushed before submit ran"
        (:app/q (state app)) => "go"
        ":on-submit received the effective (buffered) value"
        @submitted => "go")))

  (component "an external state change wins over an in-flight buffer"
    (let [app (new-app)
          t   (term/string-terminal {:rows 6 :cols 30})]
      (app/attach! app t)
      (app/step! app {:key "a" :char "a"})
      ;; external mutation while the buffer holds "a" (based-on "")
      (comp/transact! app [(set-q {:v "EXT"})])
      (app/render! app)
      (assertions
        "the external value is displayed (buffer dropped, prop authoritative)"
        (nth (app/screen-of app) 0) => "EXT                           "
        "the stale buffer was cleared"
        (engine/get-input-buffer app :q) => nil)
      (settle! app)
      (assertions
        "the superseded debounced :on-change was cancelled — the external value stays"
        (:app/q (state app)) => "EXT"))))
