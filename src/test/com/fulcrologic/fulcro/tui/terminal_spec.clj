(ns com.fulcrologic.fulcro.tui.terminal-spec
  (:require
    [clojure.string :as str]
    [com.fulcrologic.fulcro.tui.terminal :as sut]
    [fulcro-spec.core :refer [=> assertions component specification]]))

(specification {:covers {`sut/single-codepoint-string? "a28c40"}} "single-codepoint-string?"
  (assertions
    "is true for a single ASCII character"
    (sut/single-codepoint-string? "a") => true
    "is true for an astral/supplementary code point (2 UTF-16 units, 1 code point)"
    (sut/single-codepoint-string? "😀") => true             ; 😀
    "is true for a multi-byte BMP character"
    (sut/single-codepoint-string? "é") => true
    "is false for a multi-character string"
    (sut/single-codepoint-string? "ab") => false
    "is false for an empty string"
    (sut/single-codepoint-string? "") => false
    "is false for a non-string"
    (sut/single-codepoint-string? 97) => false))

(specification {:covers {`sut/key-event "634a8b"}} "key-event"
  (component "single-arg arity"
    (assertions
      "defaults char to nil and all modifiers to false"
      (sut/key-event :enter) => {:key :enter :char nil :ctrl? false :alt? false :shift? false}
      "accepts a printable 1-char key"
      (sut/key-event "a") => {:key "a" :char nil :ctrl? false :alt? false :shift? false}))
  (component "two-arg arity"
    (assertions
      "merges the provided opts over the defaults"
      (sut/key-event "a" {:char "a" :raw 97}) => {:key "a" :char "a" :ctrl? false :alt? false :shift? false :raw 97}
      "lets opts override modifier defaults"
      (:ctrl? (sut/key-event "a" {:ctrl? true})) => true)))

(def ESC (str (char 27)))

(specification {:covers {`sut/cursor-position-string "1029c4"}} "cursor-position-string"
  (assertions
    "converts 0-based (x,y) to a 1-based ANSI CUP sequence (ESC[row;colH)"
    (sut/cursor-position-string 0 0) => (str ESC "[1;1H")
    "uses y as the row and x as the column"
    (sut/cursor-position-string 4 2) => (str ESC "[3;5H")))

(specification {:covers {`sut/decode-key "339da7,1b49db"}} "decode-key"
  (component "empty input"
    (assertions
      "returns nil when there are no code points"
      (sut/decode-key []) => nil))

  (component "printable code points"
    (assertions
      "decodes a printable ASCII char with :key and :char equal to the 1-char string"
      (first (sut/decode-key [97])) => {:key "a" :char "a" :ctrl? false :alt? false :shift? false :raw 97}
      "consumes exactly one code point, leaving the rest"
      (second (sut/decode-key [97 98])) => [98]
      "decodes a multi-byte BMP code point as printable"
      (select-keys (first (sut/decode-key [0x00E9])) [:key :char]) => {:key "é" :char "é"}
      "decodes an astral/supplementary code point as printable"
      (select-keys (first (sut/decode-key [0x1F600])) [:key :char]) => {:key "😀" :char "😀"}))

  (component "named control bytes"
    (assertions
      "9 decodes to :tab"
      (:key (first (sut/decode-key [9]))) => :tab
      "13 decodes to :enter"
      (:key (first (sut/decode-key [13]))) => :enter
      "10 decodes to :enter"
      (:key (first (sut/decode-key [10]))) => :enter
      "127 decodes to :backspace"
      (:key (first (sut/decode-key [127]))) => :backspace
      "8 decodes to :backspace"
      (:key (first (sut/decode-key [8]))) => :backspace
      "named control bytes carry a nil :char"
      (:char (first (sut/decode-key [9]))) => nil))

  (component "lone ESC"
    (assertions
      "27 with nothing following decodes to :escape"
      (:key (first (sut/decode-key [27]))) => :escape
      "27 with a non-CSI follower decodes to :escape leaving the follower"
      (sut/decode-key [27 97]) => [{:key :escape :char nil :ctrl? false :alt? false :shift? false :raw 27} [97]]))

  (component "CSI arrow sequences"
    (assertions
      "27 91 65 decodes to :up"
      (:key (first (sut/decode-key [27 91 65]))) => :up
      "27 91 66 decodes to :down"
      (:key (first (sut/decode-key [27 91 66]))) => :down
      "27 91 67 decodes to :right"
      (:key (first (sut/decode-key [27 91 67]))) => :right
      "27 91 68 decodes to :left"
      (:key (first (sut/decode-key [27 91 68]))) => :left
      "consumes the whole 3-byte arrow sequence"
      (second (sut/decode-key [27 91 65 97])) => [97]))

  (component "CSI edit/navigation sequences"
    (assertions
      "27 91 51 126 decodes to :delete"
      (:key (first (sut/decode-key [27 91 51 126]))) => :delete
      "27 91 72 decodes to :home"
      (:key (first (sut/decode-key [27 91 72]))) => :home
      "27 91 70 decodes to :end"
      (:key (first (sut/decode-key [27 91 70]))) => :end
      "27 91 90 (ESC [ Z) decodes to :backtab (Shift-Tab)"
      (:key (first (sut/decode-key [27 91 90]))) => :backtab
      "27 91 49 126 decodes to :home"
      (:key (first (sut/decode-key [27 91 49 126]))) => :home
      "27 91 52 126 decodes to :end"
      (:key (first (sut/decode-key [27 91 52 126]))) => :end
      "27 91 53 126 decodes to :page-up"
      (:key (first (sut/decode-key [27 91 53 126]))) => :page-up
      "27 91 54 126 decodes to :page-down"
      (:key (first (sut/decode-key [27 91 54 126]))) => :page-down
      "consumes the whole 4-byte sequence"
      (second (sut/decode-key [27 91 51 126 97])) => [97]))

  (component "control combos"
    (assertions
      "1 decodes to ctrl+a"
      (first (sut/decode-key [1])) => {:key "a" :char nil :ctrl? true :alt? false :shift? false :raw 1}
      "26 decodes to ctrl+z"
      (select-keys (first (sut/decode-key [26])) [:key :ctrl?]) => {:key "z" :ctrl? true}
      "3 decodes to ctrl+c"
      (select-keys (first (sut/decode-key [3])) [:key :ctrl?]) => {:key "c" :ctrl? true}))

  ;; CSI-u (Kitty/fixterms) sequences encode the codepoint as ASCII decimal digits, then an optional
  ;; `; <modifiers>` (1 + bitmask: 1=shift, 2=alt, 4=ctrl), terminated by `u` (117). Helper builds the
  ;; byte sequence for a 1-char key with the given modifier field.
  (letfn [(csi-u [k mods]
            (let [cp     (int (first k))
                  digits (mapv int (str cp))
                  mod-ds (mapv int (str mods))]
              (vec (concat [27 91] digits [59] mod-ds [117]))))]
    (component "CSI-u modified-key sequences"
      (assertions
        "alt+s (mod 3) decodes to {:key \"s\" :alt? true} with a nil :char"
        (select-keys (first (sut/decode-key (csi-u "s" 3))) [:key :char :ctrl? :alt? :shift?])
        => {:key "s" :char nil :ctrl? false :alt? true :shift? false}
        "ctrl+k (mod 5) decodes to {:key \"k\" :ctrl? true} with a nil :char"
        (select-keys (first (sut/decode-key (csi-u "k" 5))) [:key :char :ctrl? :alt? :shift?])
        => {:key "k" :char nil :ctrl? true :alt? false :shift? false}
        "shift+a (mod 2) is text: keeps :char and sets :shift?"
        (select-keys (first (sut/decode-key (csi-u "a" 2))) [:key :char :shift?])
        => {:key "a" :char "a" :shift? true}
        "alt+shift+x (mod 4) sets both :alt? and :shift?"
        (select-keys (first (sut/decode-key (csi-u "x" 4))) [:ctrl? :alt? :shift?])
        => {:ctrl? false :alt? true :shift? true}
        "consumes exactly the CSI-u sequence, leaving trailing bytes"
        (second (sut/decode-key (conj (csi-u "s" 3) 98))) => [98]
        "a CSI-u sequence with no modifier field (ESC [ <cp> u) decodes the bare key"
        (select-keys (first (sut/decode-key [27 91 49 49 53 117])) [:key :char]) => {:key "s" :char "s"}))))

;; =============================================================================
;; Fake terminal (string-terminal) integration-style tests
;; =============================================================================

(specification "string-terminal"
  (component "t-read-key dequeuing"
    (let [a (sut/key-event "a" {:char "a"})
          b (sut/key-event :enter)
          t (sut/string-terminal {:keys [a b]})]
      (assertions
        "returns the scripted events in order"
        (sut/t-read-key t) => a
        (sut/t-read-key t) => b
        "returns nil once the queue is exhausted"
        (sut/t-read-key t) => nil)))

  (component "feed! enqueues more events"
    (let [t (sut/string-terminal {:keys []})
          a (sut/key-event "a" {:char "a"})]
      (sut/feed! t a)
      (assertions
        "the fed event becomes available to read"
        (sut/t-read-key t) => a
        "and the queue is empty afterward"
        (sut/t-read-key t) => nil)))

  (component "t-write!/output accumulation"
    (let [t (sut/string-terminal {})]
      (sut/t-write! t "foo")
      (sut/t-write! t "bar")
      (assertions
        "accumulates all written strings in order"
        (sut/output t) => "foobar")))

  (component "t-set-cursor!/cursor"
    (let [t (sut/string-terminal {})]
      (assertions
        "cursor is nil before any set"
        (sut/cursor t) => nil)
      (sut/t-set-cursor! t 3 7 true)
      (assertions
        "records the last cursor position and visibility"
        (sut/cursor t) => {:x 3 :y 7 :visible? true}
        "a later set overwrites the recorded cursor"
        (do (sut/t-set-cursor! t 1 1 false) (sut/cursor t)) => {:x 1 :y 1 :visible? false})))

  (component "t-size/resize!"
    (let [t (sut/string-terminal {:rows 10 :cols 40})]
      (assertions
        "reports the configured dimensions"
        (sut/t-size t) => {:rows 10 :cols 40})
      (sut/resize! t 30 100)
      (assertions
        "reports the new dimensions after resize!"
        (sut/t-size t) => {:rows 30 :cols 100})))

  (component "t-on-resize! / resize! handler"
    (let [t     (sut/string-terminal {:rows 10 :cols 40})
          calls (atom 0)
          seen  (atom nil)]
      (sut/t-on-resize! t (fn [] (swap! calls inc) (reset! seen (sut/t-size t))))
      (sut/resize! t 20 60)
      (assertions
        "resize! invokes the registered handler"
        @calls => 1
        "the handler observes the already-updated new dimensions"
        @seen => {:rows 20 :cols 60})
      (sut/t-on-resize! t nil)
      (sut/resize! t 5 5)
      (assertions
        "registering nil clears the handler (a later resize! does not call it)"
        @calls => 1
        "resize! still updates the dimensions with no handler registered"
        (sut/t-size t) => {:rows 5 :cols 5})))

  (component "default dimensions"
    (assertions
      "defaults to 24 rows x 80 cols when unspecified"
      (sut/t-size (sut/string-terminal {})) => {:rows 24 :cols 80}))

  (component "t-sync-supported? reflects the opts flag"
    (assertions
      "is true when :sync? is true"
      (sut/t-sync-supported? (sut/string-terminal {:sync? true})) => true
      "is false by default"
      (sut/t-sync-supported? (sut/string-terminal {})) => false))

  (component "t-enhanced-keys? reflects the opts flag"
    (assertions
      "is true when :enhanced-keys? is true"
      (sut/t-enhanced-keys? (sut/string-terminal {:enhanced-keys? true})) => true
      "is false by default"
      (sut/t-enhanced-keys? (sut/string-terminal {})) => false))

  (component "t-enter!/t-leave! record state"
    (let [t (sut/string-terminal {})]
      (sut/t-enter! t)
      (sut/t-leave! t)
      (assertions
        "t-enter! and t-leave! are no-op writers (do not corrupt output)"
        (sut/output t) => ""))))

(specification "full-screen enter/leave control sequences"
  ;; The CSI bodies are matched without the leading ESC byte (each is uniquely identifying anyway), so
  ;; the assertions stay ESC-free and readable.
  (let [enter   (sut/screen-enter-ansi)
        leave-e (sut/screen-leave-ansi true)
        leave-p (sut/screen-leave-ansi false)]
    (assertions
      "enter switches to the alternate screen buffer"
      (str/includes? enter "[?1049h") => true
      "enter DISABLES auto-wrap (DECAWM ?7l) so an over-wide line clips instead of spilling onto the next row"
      (str/includes? enter "[?7l") => true
      "enter hides the hardware cursor"
      (str/includes? enter "[?25l") => true
      "auto-wrap is turned off AFTER entering the alt screen, so it applies to the alt buffer"
      (< (str/index-of enter "[?1049h") (str/index-of enter "[?7l")) => true

      "leave RE-ENABLES auto-wrap (DECAWM ?7h) — the inverse of enter"
      (str/includes? leave-e "[?7h") => true
      "leave shows the cursor and returns to the primary screen"
      [(str/includes? leave-e "[?25h") (str/includes? leave-e "[?1049l")] => [true true]
      "auto-wrap is restored BEFORE leaving the alt screen"
      (< (str/index-of leave-e "[?7h") (str/index-of leave-e "[?1049l")) => true
      "the pushed enhanced-keyboard flags are popped only when they were enabled"
      [(str/includes? leave-e "[<1u") (str/includes? leave-p "[<1u")] => [true false])))
