(require 'proof)
(require 'certicrypt-syntax)
(require 'certicrypt-hooks)
(require 'certicrypt-abbrev)
;(load-library "hideshow")


(add-to-list 'hs-special-modes-alist
  '(certicrypt-mode "{" "}" "/[*/]" nil nil))

;(add-hook 'certicrypt-mode-hook 'hs-minor-mode)


(defcustom certicrypt-prog-name "easycrypt -emacs"
  "*Name of program to run CertiCrypt."
  :type 'file
  :group 'certicrypt)

(defcustom certicrypt-web-page
  "http://certicrypt.gforge.inria.fr"
  "URL of web page for CertiCrypt."
  :type 'string
  :group 'certicrypt-config)

;(defconst certicrypt-outline-regexp
;  (concat (proof-ids-to-regexp test) "[ \t]*\\(?:" "\\)" )
;  "Outline regexp for CertiCrypt games documents")

;;
;; ======== Configuration of generic modes ========
;;

(defun certicrypt-config ()
  "Configure Proof General scripting for CertiCrypt."
  (certicrypt-init-output-syntax-table)
  
  (setq  proof-terminal-string                 certicrypt-terminal-string)
  (setq  proof-script-command-end-regexp       certicrypt-end-command-regexp)
  (setq  proof-script-comment-start            "(*"
         proof-script-comment-end              "*)")
  
  ;; For undo
  (setq  proof-find-and-forget-fn              'certicrypt-find-and-forget
         proof-completed-proof-behaviour       nil)
         ;proof-kill-goal-command               "abort;;")

  (set (make-local-variable 'comment-quote-nested) nil)


  ;; For func-menu and finding goal...save regions
  (setq  proof-goal-command-p                  'certicrypt-goal-command-p
         proof-save-command-regexp             "save"
			proof-really-save-command-p           'certicrypt-save-command-p
         proof-goal-with-hole-regexp           certicrypt-named-entity-regexp
         proof-goal-with-hole-result           1
         proof-save-with-hole-regexp           nil
         proof-script-imenu-generic-expression certicrypt-generic-expression)
         ;imenu-syntax-alist-                   certicrypt-script-syntax-table-alist)
  
  (setq  proof-goal-command                    "equiv %s:"
         proof-save-command                    "save") 
  
  (setq  proof-prog-name                       certicrypt-prog-name
         proof-assistant-home-page             certicrypt-web-page)

  ; Options
  (setq  proof-three-window-enable             t
         proof-auto-multiple-files             t)
  ;(set (make-local-variable 'outline-regexp)   "game" );certicrypt-outline-regexp)  

  ; Setting indents 
  (set   (make-local-variable 'indent-tabs-mode) nil)
  (setq  proof-indent-enclose-offset   (- proof-indent)
         proof-indent-open-offset     0
         proof-indent-close-offset    0
         ;proof-indent-inner-regexp    certicrypt-indent-inner-regexp
         proof-indent-any-regexp      certicrypt-indent-any-regexp
         proof-indent-enclose-regexp  certicrypt-indent-enclose-regexp
         proof-indent-open-regexp     certicrypt-indent-open-regexp
         proof-indent-close-regexp    certicrypt-indent-close-regexp)

  (certicrypt-init-syntax-table)
  ;; we can cope with nested comments
  (set (make-local-variable 'comment-quote-nested) nil)

  (setq  proof-script-font-lock-keywords
         certicrypt-font-lock-keywords))


(defun certicrypt-shell-config ()
  "Configure Proof General shell for CertiCrypt."
  (certicrypt-init-output-syntax-table)
  (setq  proof-shell-auto-terminate-commands     certicrypt-terminal-string)
  (setq  proof-shell-eager-annotation-start      "^\\[info\\]")
  (setq  proof-shell-strip-crs-from-input        nil)
  (setq  proof-shell-annotated-prompt-regexp     "^\\[[0-9]+|[0-9]+|[TF]|[0-9]+|[0-9]+\\]>")
  (setq  proof-shell-clear-goals-regexp
         certicrypt-shell-proof-completed-regexp)
  (setq  proof-shell-proof-completed-regexp 
         certicrypt-shell-proof-completed-regexp)
  (setq  proof-shell-error-regexp  certicrypt-error-regexp)
  (setq  proof-shell-truncate-before-error nil)
  (setq  proof-shell-quit-cmd                    "Drop;; \n quit();;")
  (setq  proof-shell-start-goals-regexp          "^Current")
  (setq  proof-shell-end-goals-regexp nil)  ; up to next prompt
  (setq  proof-shell-font-lock-keywords 
         certicrypt-font-lock-keywords))


;;
;; ======== Defining the derived modes ========
;;
;; The derived modes set the variables, then call the
;; <mode>-config-done function to complete configuration.

(define-derived-mode certicrypt-mode proof-mode
  "CertiCrypt script" nil
  (certicrypt-config)
  (proof-config-done))

(define-derived-mode certicrypt-shell-mode proof-shell-mode
  "CertiCrypt shell" nil
  (certicrypt-shell-config)
  (proof-shell-config-done))

(define-derived-mode certicrypt-response-mode proof-response-mode
  "CertiCrypt response" nil
  (certicrypt-init-output-syntax-table)
  (setq  proof-response-font-lock-keywords 
         certicrypt-font-lock-keywords)
  (proof-response-config-done))

(define-derived-mode certicrypt-goals-mode proof-goals-mode
  "CertiCrypt goals" nil
  (certicrypt-init-output-syntax-table)
  (setq  proof-goals-font-lock-keywords 
         certicrypt-font-lock-keywords)
  (proof-goals-config-done))

(defun certicrypt-get-last-error-location () 
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


(defun certicrypt-advance-until-command ()
   (while (proof-looking-at "\\s-")
			 (forward-char 1)))

(defun certicrypt-highlight-error () 
  "Use 'certicrypt-get-last-error-location' to know the position
  of the error and then highlight in the script buffer"
  (proof-with-current-buffer-if-exists proof-script-buffer
    (let ((mtch (certicrypt-get-last-error-location)))
		(when mtch
		  (let ((pos (car mtch))
				  (lgth (cadr mtch)))
          (if (eq (proof-unprocessed-begin) (point-min))
				(goto-char (proof-unprocessed-begin))
				(goto-char (+ (proof-unprocessed-begin) 1)))
		    (certicrypt-advance-until-command)
			 (goto-char (+ (point) pos))
			 (span-make-self-removing-span (point) (+ (point) lgth)
												;	 'face 'proof-script-sticky-error-face))))))
													 'face 'proof-script-highlight-error-face))))))


(defun certicrypt-highlight-error-hook ()
  (certicrypt-highlight-error ))

(add-hook 'proof-shell-handle-error-or-interrupt-hook 'certicrypt-highlight-error-hook t)

(provide 'certicrypt)
