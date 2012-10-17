(require 'proof-syntax)
(require 'certicrypt-keywords)
(require 'certicrypt-hooks)

;; Check me
(defconst certicrypt-keywords-proof-goal 
  '("equiv [^auto]"))

(defconst certicrypt-keywords-proof-save
  '("save"))

(defconst certicrypt-keywords-code-open
  '("{" ))

(defconst certicrypt-keywords-code-close
  '("}" )) 


(defconst certicrypt-keywords-code-end
  '(";;" ";" )) 

(defconst certicrypt-keywords-major
  '(  
      "type"
      "op"
      "game"
      "Main"
      "fun"
      "abs"
      "prover"
      "adversary"
      "cnst"
      "axiom"
      "lemma"
      "equiv"
      "claim"
      "unset"
      "if"
      "var"
      "return"
))


(defconst certicrypt-keywords-index
  '( "type" "op" "pop" "cnst" "game" "adversary" "claim" "equiv"))

;; End check me

(defvar certicrypt-other-symbols "\\(\\.\\.\\|\\[\\]\\)")


(defvar certicrypt-operator-char-1 "=\\|<\\|>\\|~")
(defvar certicrypt-operator-char-2 "\\+\\|\\-")
(defvar certicrypt-operator-char-3 "\\*\\|/\\|%")
(defvar certicrypt-operator-char-4 "!\\|\\$\\|&\\|\\?\\|@\\|\\^\\|:\\||\\|#")

(defvar certicrypt-operator-char-1234
  (concat "\\(" certicrypt-operator-char-1
          "\\|" certicrypt-operator-char-2
			 "\\|" certicrypt-operator-char-3
			 "\\|" certicrypt-operator-char-4 "\\)"))



(defconst certicrypt-id "[A-Za-z_]+")
(defconst certicrypt-terminal-string ".")

;; For imenu
(defconst  certicrypt-keywords-imenu
  (append 
	  certicrypt-keywords-index))

(defconst  certicrypt-entity-regexp
  (concat "\\(" (proof-ids-to-regexp certicrypt-keywords-imenu) "\\)"))

(defconst  certicrypt-named-regexp
  (concat "\\s *\\(" certicrypt-id "\\)\\s *"))

(defconst  certicrypt-named-entity-regexp
  (concat certicrypt-entity-regexp
    "\\ *"
    certicrypt-named-regexp
    "\\ *[:=]"))


(defconst  certicrypt-generic-expression
  (mapcar  (lambda (kw)
    (list 
      (capitalize kw)
      (concat "\\ *" kw "\\ +\\([A-Za-z0-9_]+\\)\\ *[:=]")
      1))
    certicrypt-keywords-imenu))


(defun certicrypt-save-command-p (span str)
  "Decide whether argument is a Save command or not"
  (and (proof-string-match-safe "save" (or (span-property span 'cmd) ""))
       (if (= certicrypt-last-but-one-proofdepth 1) t nil)))

(defun certicrypt-goal-command-p (span)
  "Is SPAN a goal?  Decide by matching with `'equiv .... [^auto]'"
  (and (proof-string-match-safe "equiv" (or (span-property span 'cmd) ""))
       (or (proof-string-match-safe "[^auto]" (or (span-property span 'cmd) ""))
           (proof-string-match-safe "eager" (or (span-property span 'cmd) "")))))


(defconst certicrypt-end-command-regexp "[^\\.]\\.\\(\\s \\|\n\\|$\\)")


(defun certicrypt-init-output-syntax-table ()
  "Set appropriate values for syntax table for CertiCrypt output."
  (modify-syntax-entry ?`   " ")
  (modify-syntax-entry ?,   " ")
  (modify-syntax-entry ?\'  "_")
  (modify-syntax-entry ?_   "_")

  ;; For comments
  (modify-syntax-entry ?\* ". 23") 

  ;; For blocks
  (modify-syntax-entry ?\( "()1")
  (modify-syntax-entry ?\) ")(4")
  (modify-syntax-entry ?\{ "(}")
  (modify-syntax-entry ?\} "){")
  (modify-syntax-entry ?\[ "(]")
  (modify-syntax-entry ?\] ")["))

;
;; ----- regular expressions

(defvar certicrypt-error-regexp "^\\[error\\]"
  "A regexp indicating that the CertiCrypt process has identified an error.")


(defvar certicrypt-shell-proof-completed-regexp "QED"
  "*Regular expression indicating that the proof has been completed.")


(defconst certicrypt-any-command-regexp
  ;; allow terminator to be considered as command start:
  ;; FIXME: really needs change in generic function to take account of this,
  ;; since the end character of a command is not the start
  (concat "\\(\\s(\\|\\s)\\|\\sw\\|\\s \\|\\s_\\)*="  ;match assignments
          "\\|;;\\|;\\|" 
          (proof-ids-to-regexp certicrypt-keywords-major))
  "Regexp matching any CertiCrypt command start or the terminator character.")



(defconst certicrypt-keywords-indent-open
  (append certicrypt-keywords-proof-goal
          certicrypt-keywords-code-open))

(defconst certicrypt-keywords-indent-close
  (append certicrypt-keywords-proof-save
          certicrypt-keywords-code-close))

(defconst certicrypt-keywords-indent-enclose
  (append certicrypt-keywords-code-open
          certicrypt-keywords-code-close
          certicrypt-keywords-code-end
          certicrypt-keywords-proof-goal
          certicrypt-keywords-proof-save))

; Regular expression for indentation

(defconst certicrypt-indent-any-regexp
  (proof-regexp-alt certicrypt-any-command-regexp "\\s(" "\\s)"))
    
(defconst certicrypt-indent-inner-regexp
  (proof-regexp-alt "[{}[]()]"))

(defconst certicrypt-indent-enclose-regexp
  (proof-regexp-alt (proof-ids-to-regexp certicrypt-keywords-indent-enclose) "\\s)"))

(defconst certicrypt-indent-open-regexp
  (proof-regexp-alt (proof-ids-to-regexp certicrypt-keywords-indent-open) "\\s("))

(defconst certicrypt-indent-close-regexp
  (proof-regexp-alt (proof-ids-to-regexp certicrypt-keywords-indent-close) "\\s)"))

(defvar certicrypt-font-lock-keywords
  (list
    (cons (proof-ids-to-regexp certicrypt-program-keywords) 
        'font-lock-keyword-face)
			; 'proof-declaration-name-face)
    (cons (proof-ids-to-regexp certicrypt-tactics-keywords) 
          'proof-tactics-name-face)
    (cons (proof-ids-to-regexp certicrypt-tactics2-keywords) 
          'proof-tactics-name-face)

	 (cons (concat certicrypt-operator-char-1234 "+") 'font-lock-type-face)

	 (cons certicrypt-other-symbols
          'font-lock-type-face)

    (cons (proof-ids-to-regexp certicrypt-common-keywords)  
        'font-lock-keyword-face)))
          ;'font-lock-type-face)))

(defun certicrypt-init-syntax-table ()
  "Set appropriate values for syntax table in current buffer."
  (modify-syntax-entry ?\$ ".")
  (modify-syntax-entry ?\/ ".")
  (modify-syntax-entry ?\\ ".")
  (modify-syntax-entry ?+  ".")
  (modify-syntax-entry ?-  ".")
  (modify-syntax-entry ?=  ".")
  (modify-syntax-entry ?%  ".")
  (modify-syntax-entry ?<  ".")
  (modify-syntax-entry ?>  ".")
  (modify-syntax-entry ?\& ".")
  (modify-syntax-entry ?_  "_")
  (modify-syntax-entry ?\' "_")
  (modify-syntax-entry ?\| ".")
  (modify-syntax-entry ?\. ".")
  (modify-syntax-entry ?\* ". 23n")
  (modify-syntax-entry ?\( "()1")
  (modify-syntax-entry ?\) ")(4"))

(provide 'certicrypt-syntax)

