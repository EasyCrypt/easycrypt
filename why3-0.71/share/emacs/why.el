
;; why.el - GNU Emacs mode for Why
;; Copyright (C) 2002 Jean-Christophe FILLIATRE

(defvar why-mode-hook nil)

(defvar why-mode-map nil
  "Keymap for Why major mode")

(if why-mode-map nil
  (setq why-mode-map (make-keymap))
  (define-key why-mode-map "\C-c\C-c" 'why-generate-obligations)
  (define-key why-mode-map "\C-c\C-a" 'why-find-alternate-file)
  (define-key why-mode-map "\C-c\C-v" 'why-viewer)
  (define-key why-mode-map [(control return)] 'font-lock-fontify-buffer))

(setq auto-mode-alist
      (append
       '(("\\.mlw" . why-mode))
       auto-mode-alist))

;; font-lock

(defun why-regexp-opt (l)
  (concat "\\<" (concat (regexp-opt l t) "\\>")))

(defconst why-font-lock-keywords-1
  (list
   ;; Note: comment font-lock is guaranteed by suitable syntax entries
   '("(\\*\\([^*)]\\([^*]\\|\\*[^)]\\)*\\)?\\*)" . font-lock-comment-face)
   '("{}\\|{[^|]\\([^}]*\\)}" . font-lock-type-face)
   `(,(why-regexp-opt '("use" "clone" "namespace" "import" "export" "inductive" "external" "function" "predicate" "val" "exception" "axiom" "lemma" "goal" "type" "mutable" "model" "abstract" "reads" "writes" "raises")) . font-lock-builtin-face)
   `(,(why-regexp-opt '("any" "match" "let" "rec" "in" "if" "then" "else" "begin" "end" "while" "invariant" "variant" "for" "to" "downto" "do" "done" "label" "loop" "assert" "absurd" "assume" "check" "ghost" "try" "with" "theory" "uses" "module")) . font-lock-keyword-face)
   ; `(,(why-regexp-opt '("unit" "bool" "int" "float" "prop" "array")) . font-lock-type-face)
   )
  "Minimal highlighting for Why mode")

(defvar why-font-lock-keywords why-font-lock-keywords-1
  "Default highlighting for Why mode")

(defvar why-indent 2
  "How many spaces to indent in why mode.")
(make-variable-buffer-local 'why-indent)

;; syntax

(defvar why-mode-syntax-table nil
  "Syntax table for why-mode")

(defun why-create-syntax-table ()
  (if why-mode-syntax-table
      ()
    (setq why-mode-syntax-table (make-syntax-table))
    (set-syntax-table why-mode-syntax-table)
    (modify-syntax-entry ?' "w" why-mode-syntax-table)
    (modify-syntax-entry ?_ "w" why-mode-syntax-table)
    ; comments
    (modify-syntax-entry ?\( ". 1" why-mode-syntax-table)
    (modify-syntax-entry ?\) ". 4" why-mode-syntax-table)
    (modify-syntax-entry ?* ". 23" why-mode-syntax-table)
    ))

;; utility functions 

(defun why-go-and-get-next-proof ()
  (let ((bp (search-forward "Proof." nil t)))
    (if (null bp) (progn (message "Cannot find a proof below") nil)
      (let ((bs (re-search-forward "Save\\|Qed\\." nil t)))
	(if (null bs) (progn (message "Cannot find a proof below") nil)
	  (if (> bs (+ bp 6))
	      (let ((br (+ bp 1))
		    (er (progn (goto-char bs) (beginning-of-line) (point))))
		(progn (kill-region br er) t))
	    (why-go-and-get-next-proof)))))))

(defun why-grab-next-proof ()
  "grab the next non-empty proof below and insert it at current point"
  (interactive)
  (if (save-excursion (why-go-and-get-next-proof)) (yank)))

;; custom variables

(require 'custom)

(defcustom why-prover "coq"
  "Why prover"
  :group 'why :type '(choice (const :tag "Coq" "coq")
			     (const :tag "PVS" "pvs")))

(defcustom why-prog-name "why"
  "Why executable name"
  :group 'why :type 'string)

(defcustom why-options "--valid"
  "Why options"
  :group 'why :type 'string)

(defcustom why-viewer-prog-name "why_viewer"
  "Why viewer executable name"
  :group 'why :type 'string)

(defun why-command-line (file)
  (concat why-prog-name " -P " why-prover " " why-options " " file))

(defun why-find-alternate-file ()
  "switch to the proof obligations buffer"
  (interactive)
  (let* ((f (buffer-file-name))
	 (fcoq (concat (file-name-sans-extension f) "_why.v")))
    (find-file fcoq)))

(defun why-generate-obligations ()
  "generate the proof obligations"
  (interactive)
  (let ((f (buffer-name)))
    (compile (why-command-line f))))

(defun why-viewer-command-line (file)
  (concat why-viewer-prog-name " " file))

(defun why-viewer ()
  "launch the why viewer"
  (interactive)
  (let ((f (buffer-name)))
    (compile (why-viewer-command-line f))))

(defun why-generate-ocaml ()
  "generate the ocaml code"
  (interactive)
  (let ((f (buffer-name)))
    (compile (concat why-prog-name " --ocaml " f))))

;; menu

(require 'easymenu)

(defun why-menu ()
  (easy-menu-define
   why-mode-menu (list why-mode-map)
   "Why Mode Menu." 
   '("Why"
     ["Customize Why mode" (customize-group 'why) t]
     "---"
     ["Type-check buffer" why-type-check t]
     ; ["Show WP" why-show-wp t]
     ["Why viewer" why-viewer t]
     ["Generate obligations" why-generate-obligations t]
     ["Switch to obligations buffer" why-find-alternate-file t]
     ["Generate Ocaml code" why-generate-ocaml t]
     ["Recolor buffer" font-lock-fontify-buffer t]
     "---"
     "Coq"
     ["Grab next proof" why-grab-next-proof t]
     "---"
     "PVS"
     "---"
     ))
  (easy-menu-add why-mode-menu))

;indentation

;http://www.emacswiki.org/emacs/ModeTutorial
(defun why-indent-line ()
  "Indent current line as why logic"
  (interactive)
  (save-excursion
    (beginning-of-line)
    ;(debug)
    (if (bobp)  ; Check for rule 1
        (indent-line-to 0)
      (let ((not-indented t) cur-indent)
        (if (looking-at "^[ \t]*end") ; Check for rule 2
            (progn
              (save-excursion
                (forward-line -1)
                (setq cur-indent (- (current-indentation) why-indent)))
              (if (< cur-indent 0)
                  (setq cur-indent 0)))
          (progn
            (if (looking-at "^[ \t]*\\(logic\\|type\\|prop\\)") ; check for clone 
                (progn
                  (save-excursion
                    (forward-line -1)
                    (if (looking-at "^[ \t]*\\(logic\\|type\\|prop\\).*,[ \t]*$")
                        (progn 
                          (setq cur-indent (current-indentation))
                          (setq not-indented nil))
                      (if (looking-at "^[ \t]*clone.*with ")
                          (progn 
                            (setq cur-indent (+ (current-indentation) why-indent))
                            (setq not-indented nil)
                            ))))))
        ;For the definition its very badly done...
          (if (looking-at "^[ \t]*$")
	      ;; (save-excursion 
	      ;; 	(forward-line -1)
	      ;; 	(setq cur-indent (current-indentation))
	      ;; 	(setq not-indented nil))
              (progn
                (setq cur-indent 0)
                (setq not-indented nil))
	    (if (not
		 (looking-at "^[ \t]*(\*.*"))
            (if (not 
                 (looking-at "^[ \t]*\\(logic\\|type\\|axiom\\|goal\\|lemma\\|inductive\\|use\\|theory\\|clone\\)"))
                (save-excursion
                  (condition-case nil
                      (save-excursion 
                        (backward-up-list)
                        (setq cur-indent (+ (current-column) 1))
                        (setq not-indented nil))
                    (error 
                     (forward-line -1)
                     (if (looking-at  
                          "^[ \t]*\\(logic\\|type\\|axiom\\|goal\\|lemma\\|inductive\\)")
                         (setq cur-indent (+ (current-indentation) why-indent))
                       (setq cur-indent (current-indentation)))
                     (setq not-indented nil)))))))
          ;For inside theory or namespace
          (save-excursion 
            (while not-indented
              (forward-line -1)
              (if (looking-at "^[ \t]*end") ; Check for rule 3
                  (progn
                    (setq cur-indent (current-indentation))
                    (setq not-indented nil))
                                        ; Check for rule 4
                (if (looking-at "^[ \t]*\\(theory\\|namespace\\)")
                    (progn
                      (setq cur-indent (+ (current-indentation) why-indent))
                      (setq not-indented nil))
                  (if (bobp) ; Check for rule 5
                      (setq not-indented nil)))))))
        (if cur-indent
            (indent-line-to cur-indent)
          (indent-line-to 0)))))))

;; setting the mode
(defun why-mode ()
  "Major mode for editing Why programs.

\\{why-mode-map}"
  (interactive)
  (kill-all-local-variables)
  (why-create-syntax-table)
  ; hilight
  (make-local-variable 'font-lock-defaults)
  (setq font-lock-defaults '(why-font-lock-keywords))
  ; indentation
  (make-local-variable 'indent-line-function)
  (setq indent-line-function 'why-indent-line)
  ; OCaml style comments for comment-region, comment-dwim, etc.
  ; (setq comment-start "(\\*" comment-end "\\*)")
  ; menu
  ; providing the mode
  (setq major-mode 'why-mode)
  (setq mode-name "WHY")
  (use-local-map why-mode-map)
  (font-lock-mode 1)
  (why-menu)
  (run-hooks 'why-mode-hook))

(provide 'why-mode)

