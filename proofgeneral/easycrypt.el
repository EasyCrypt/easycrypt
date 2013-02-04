(require 'proof)
(require 'easycrypt-syntax)
(require 'easycrypt-hooks)
(require 'easycrypt-abbrev)
;(load-library "hideshow")


(add-to-list 'hs-special-modes-alist
  '(easycrypt-mode "{" "}" "/[*/]" nil nil))

;(add-hook 'easycrypt-mode-hook 'hs-minor-mode)

(defcustom easycrypt-prog-name "easycrypt -emacs"
  "*Name of program to run EasyCrypt."
  :type 'file
  :group 'easycrypt)

(defcustom easycrypt-web-page
  "http://www.easycrypt.info"
  "URL of web page for EasyCrypt."
  :type 'string
  :group 'easycrypt-config)

;(defconst easycrypt-outline-regexp
;  (concat (proof-ids-to-regexp test) "[ \t]*\\(?:" "\\)" )
;  "Outline regexp for EasyCrypt games documents")

;;
;; ======== Configuration of generic modes ========
;;

(defun easycrypt-config ()
  "Configure Proof General scripting for EasyCrypt."
  (easycrypt-init-output-syntax-table)
  
  (setq  proof-terminal-string                 easycrypt-terminal-string)
  (setq  proof-script-command-end-regexp       easycrypt-end-command-regexp)
  (setq  proof-script-comment-start            "(*"
         proof-script-comment-end              "*)")
  
  ;; For undo
  (setq  proof-find-and-forget-fn              'easycrypt-find-and-forget
         proof-completed-proof-behaviour       nil)
         ;proof-kill-goal-command               "abort;;")

  (set (make-local-variable 'comment-quote-nested) nil)


  ;; For func-menu and finding goal...save regions
  (setq  proof-goal-command-p                  'easycrypt-goal-command-p
         proof-save-command-regexp             "save"
			proof-really-save-command-p           'easycrypt-save-command-p
         proof-goal-with-hole-regexp           easycrypt-named-entity-regexp
         proof-goal-with-hole-result           1
         proof-save-with-hole-regexp           nil
         proof-script-imenu-generic-expression easycrypt-generic-expression)
         ;imenu-syntax-alist-                   easycrypt-script-syntax-table-alist)
  
  (setq  proof-goal-command                    "equiv %s:"
         proof-save-command                    "save") 
  
  (setq  proof-prog-name                       easycrypt-prog-name
         proof-assistant-home-page             easycrypt-web-page)

  ; Options
  (setq  proof-three-window-enable             t
         proof-auto-multiple-files             t)
  ;(set (make-local-variable 'outline-regexp)   "game" );easycrypt-outline-regexp)  

  ; Setting indents 
  (set   (make-local-variable 'indent-tabs-mode) nil)
  (setq  proof-indent-enclose-offset   (- proof-indent)
         proof-indent-open-offset     0
         proof-indent-close-offset    0
         ;proof-indent-inner-regexp    easycrypt-indent-inner-regexp
         proof-indent-any-regexp      easycrypt-indent-any-regexp
         proof-indent-enclose-regexp  easycrypt-indent-enclose-regexp
         proof-indent-open-regexp     easycrypt-indent-open-regexp
         proof-indent-close-regexp    easycrypt-indent-close-regexp)

  (easycrypt-init-syntax-table)
  ;; we can cope with nested comments
  (set (make-local-variable 'comment-quote-nested) nil)

  (setq  proof-script-font-lock-keywords
         easycrypt-font-lock-keywords))


(defun easycrypt-shell-config ()
  "Configure Proof General shell for EasyCrypt."
  (easycrypt-init-output-syntax-table)
  (setq  proof-shell-auto-terminate-commands     easycrypt-terminal-string)
  (setq  proof-shell-eager-annotation-start      "^\\[info\\]")
  (setq  proof-shell-strip-crs-from-input        nil)
  (setq  proof-shell-annotated-prompt-regexp     "^\\[[0-9]+|[0-9]+|[TF]|[0-9]+|[0-9]+\\]>")
  (setq  proof-shell-clear-goals-regexp
         easycrypt-shell-proof-completed-regexp)
  (setq  proof-shell-proof-completed-regexp 
         easycrypt-shell-proof-completed-regexp)
  (setq  proof-shell-error-regexp  easycrypt-error-regexp)
  (setq  proof-shell-truncate-before-error nil)
  (setq  proof-shell-quit-cmd                    "Drop;; \n quit();;")
  (setq  proof-shell-start-goals-regexp          "^Current")
  (setq  proof-shell-end-goals-regexp nil)  ; up to next prompt
  (setq  proof-shell-font-lock-keywords 
         easycrypt-font-lock-keywords))


;;
;; ======== Defining the derived modes ========
;;
;; The derived modes set the variables, then call the
;; <mode>-config-done function to complete configuration.

(define-derived-mode easycrypt-mode proof-mode
  "EasyCrypt script" nil
  (easycrypt-config)
  (proof-config-done))

(define-derived-mode easycrypt-shell-mode proof-shell-mode
  "EasyCrypt shell" nil
  (easycrypt-shell-config)
  (proof-shell-config-done))

(define-derived-mode easycrypt-response-mode proof-response-mode
  "EasyCrypt response" nil
  (easycrypt-init-output-syntax-table)
  (setq  proof-response-font-lock-keywords 
         easycrypt-font-lock-keywords)
  (proof-response-config-done))

(define-derived-mode easycrypt-goals-mode proof-goals-mode
  "EasyCrypt goals" nil
  (easycrypt-init-output-syntax-table)
  (setq  proof-goals-font-lock-keywords 
         easycrypt-font-lock-keywords)
  (proof-goals-config-done))

(defun easycrypt-get-last-error-location () 
  "Remove [error] in the error message and extract the position
  and length of the error "
  (proof-with-current-buffer-if-exists proof-response-buffer
    (goto-char (point-max))

	 ; Match and remove [error]
	 (when (re-search-backward "\\(\\[error\\]\\)" nil t)
		(let ((text (match-string 1)))
		  (let ((inhibit-read-only t))
			 (delete-region (match-beginning 0) (match-end 0)))))

    (goto-char (point-max))
	 ; Extract the begin-position and end-position
    (when (re-search-backward "characters \\([0-9]+\\)-\\([0-9]+\\)" nil t)
		 (let* ((pos1 (string-to-number (match-string 1)))
				  (pos2 (string-to-number (match-string 2)))
				  (len (- pos2 pos1) ))
			(list pos1 len)))))


(defun easycrypt-advance-until-command ()
   (while (proof-looking-at "\\s-")
			 (forward-char 1)))

(defun easycrypt-highlight-error () 
  "Use 'easycrypt-get-last-error-location' to know the position
  of the error and then highlight in the script buffer"
  (proof-with-current-buffer-if-exists proof-script-buffer
    (let ((mtch (easycrypt-get-last-error-location)))
		(when mtch
		  (let ((pos (car mtch))
				  (lgth (cadr mtch)))
          (if (eq (proof-unprocessed-begin) (point-min))
				(goto-char (proof-unprocessed-begin))
				(goto-char (+ (proof-unprocessed-begin) 1)))
		    (easycrypt-advance-until-command)
			 (goto-char (+ (point) pos))
			 (span-make-self-removing-span (point) (+ (point) lgth)
												;	 'face 'proof-script-sticky-error-face))))))
													 'face 'proof-script-highlight-error-face))))))

(defun easycrypt-highlight-error-hook ()
  (easycrypt-highlight-error ))

(add-hook 'proof-shell-handle-error-or-interrupt-hook 'easycrypt-highlight-error-hook t)

(provide 'easycrypt)
