(require 'span)
(require 'proof)

(defvar easycrypt-last-but-one-statenum 0)

;; Function for set or get the information in the span
(defsubst easycrypt-get-span-statenum (span)
  "Return the state number of the SPAN."
  (span-property span 'statenum))

(defsubst easycrypt-set-span-statenum (span val)
  "Set the state number of the SPAN to VAL."
  (span-set-property span 'statenum val))

(defsubst proof-last-locked-span ()
  (with-current-buffer proof-script-buffer
  (span-at (- (proof-unprocessed-begin) 1) 'type)))

(defun easycrypt-last-prompt-info (s)
  "Extract the information from prompt."
  (let ((lastprompt (or s (error "no prompt"))))
     (when (string-match "\\[\\([0-9]+\\)]" lastprompt)
           (list (string-to-number (match-string 1 lastprompt))))))

(defun easycrypt-last-prompt-info-safe ()
  "Take from `proof-shell-last-prompt' the last information in the prompt."
  (easycrypt-last-prompt-info proof-shell-last-prompt))

(defun easycrypt-set-state-infos ()
  "Set information necessary for backtracking."
  (if proof-shell-last-prompt
     ;; infos = prompt infos of the very last prompt
     ;; sp    = last locked span, which we want to fill with prompt infos
     (let ((sp    (if proof-script-buffer (proof-last-locked-span)))
           (infos (or (easycrypt-last-prompt-info-safe) '(0))))

       (unless (or (not sp) (easycrypt-get-span-statenum sp))
         (easycrypt-set-span-statenum sp easycrypt-last-but-one-statenum))
       (setq easycrypt-last-but-one-statenum (car infos))
     )))

(add-hook 'proof-state-change-hook 'easycrypt-set-state-infos)

(defun easycrypt-find-and-forget (span)
  (let ((span-staten (easycrypt-get-span-statenum span)))
       (list (format "undo %s." (int-to-string span-staten)))))

(provide 'easycrypt-hooks)
