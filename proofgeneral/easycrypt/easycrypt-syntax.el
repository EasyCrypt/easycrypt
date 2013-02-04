(require 'proof-syntax)
(require 'easycrypt-keywords)
(require 'easycrypt-hooks)

;; Check me
(defconst easycrypt-keywords-proof-goal 
  '("equiv [^auto]"))

(defconst easycrypt-keywords-proof-save
  '("save"))

(defconst easycrypt-keywords-code-open
  '("{" ))

(defconst easycrypt-keywords-code-close
  '("}" )) 

(defconst easycrypt-keywords-code-end
  '(";;" ";")) 

(defconst easycrypt-keywords-index
  '( "type" "op" "pop" "cnst" "game" "adversary" "claim" "equiv"))

;; End check me

(defvar easycrypt-other-symbols "\\(\\.\\.\\|\\[\\]\\)")

(defvar easycrypt-operator-char-1 "=\\|<\\|>\\|~")
(defvar easycrypt-operator-char-2 "\\+\\|\\-")
(defvar easycrypt-operator-char-3 "\\*\\|/\\|%")
(defvar easycrypt-operator-char-4 "!\\|\\$\\|&\\|\\?\\|@\\|\\^\\|:\\||\\|#")

(defvar easycrypt-operator-char-1234
  (concat "\\(" easycrypt-operator-char-1
          "\\|" easycrypt-operator-char-2
			 "\\|" easycrypt-operator-char-3
			 "\\|" easycrypt-operator-char-4 "\\)"))

(defconst easycrypt-id "[A-Za-z_]+")
(defconst easycrypt-terminal-string ".")

;; For imenu
(defconst  easycrypt-keywords-imenu
  (append 
	  easycrypt-keywords-index))

(defconst  easycrypt-entity-regexp
  (concat "\\(" (proof-ids-to-regexp easycrypt-keywords-imenu) "\\)"))

(defconst  easycrypt-named-regexp
  (concat "\\s *\\(" easycrypt-id "\\)\\s *"))

(defconst  easycrypt-named-entity-regexp
  (concat easycrypt-entity-regexp
    "\\ *"
    easycrypt-named-regexp
    "\\ *[:=]"))

(defconst  easycrypt-generic-expression
  (mapcar  (lambda (kw)
    (list 
      (capitalize kw)
      (concat "\\ *" kw "\\ +\\([A-Za-z0-9_]+\\)\\ *[:=]")
      1))
    easycrypt-keywords-imenu))

(defun easycrypt-save-command-p (span str)
  "Decide whether argument is a Save command or not"
  (and (proof-string-match-safe "save" (or (span-property span 'cmd) ""))
       (if (= easycrypt-last-but-one-proofdepth 1) t nil)))

(defun easycrypt-goal-command-p (span)
  "Is SPAN a goal?  Decide by matching with `'equiv .... [^auto]'"
  (and (proof-string-match-safe "equiv" (or (span-property span 'cmd) ""))
       (or (proof-string-match-safe "[^auto]" (or (span-property span 'cmd) ""))
           (proof-string-match-safe "eager" (or (span-property span 'cmd) "")))))

(defconst easycrypt-end-command-regexp "[^\\.]\\.\\(\\s \\|\n\\|$\\)")

(defun easycrypt-init-output-syntax-table ()
  "Set appropriate values for syntax table for EasyCrypt output."
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

(defvar easycrypt-error-regexp "^\\[error\\]\\|^anomaly"
  "A regexp indicating that the EasyCrypt process has identified an error.")

(defvar easycrypt-shell-proof-completed-regexp "QED"
  "*Regular expression indicating that the proof has been completed.")

(defconst easycrypt-any-command-regexp
  ;; allow terminator to be considered as command start:
  ;; FIXME: really needs change in generic function to take account of this,
  ;; since the end character of a command is not the start
  (concat "\\(\\s(\\|\\s)\\|\\sw\\|\\s \\|\\s_\\)*="  ;match assignments
          "\\|;;\\|;\\|" 
          (proof-ids-to-regexp easycrypt-global-keywords))
  "Regexp matching any EasyCrypt command start or the terminator character.")

(defconst easycrypt-keywords-indent-open
  (append easycrypt-keywords-proof-goal
          easycrypt-keywords-code-open))

(defconst easycrypt-keywords-indent-close
  (append easycrypt-keywords-proof-save
          easycrypt-keywords-code-close))

(defconst easycrypt-keywords-indent-enclose
  (append easycrypt-keywords-code-open
          easycrypt-keywords-code-close
          easycrypt-keywords-code-end
          easycrypt-keywords-proof-goal
          easycrypt-keywords-proof-save))

; Regular expression for indentation
(defconst easycrypt-indent-any-regexp
  (proof-regexp-alt easycrypt-any-command-regexp "\\s(" "\\s)"))
    
(defconst easycrypt-indent-inner-regexp
  (proof-regexp-alt "[{}[]()]"))

(defconst easycrypt-indent-enclose-regexp
  (proof-regexp-alt (proof-ids-to-regexp easycrypt-keywords-indent-enclose) "\\s)"))

(defconst easycrypt-indent-open-regexp
  (proof-regexp-alt (proof-ids-to-regexp easycrypt-keywords-indent-open) "\\s("))

(defconst easycrypt-indent-close-regexp
  (proof-regexp-alt (proof-ids-to-regexp easycrypt-keywords-indent-close) "\\s)"))

(defvar easycrypt-font-lock-keywords
  (list
    (cons (proof-ids-to-regexp easycrypt-global-keywords)
        'font-lock-keyword-face)
    (cons (proof-ids-to-regexp easycrypt-tactic-keywords)
          'proof-tactics-name-face)
    (cons (proof-ids-to-regexp easycrypt-dangerous-keywords)
          'proof-tactics-name-face)
    (cons (proof-ids-to-regexp easycrypt-prog-keywords)  
        'font-lock-keyword-face)
    (cons (concat easycrypt-operator-char-1234 "+")
          'font-lock-type-face)
    (cons easycrypt-other-symbols
          'font-lock-type-face)))

(defun easycrypt-init-syntax-table ()
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

(provide 'easycrypt-syntax)
