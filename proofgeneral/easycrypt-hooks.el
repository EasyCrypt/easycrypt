(require 'span)
(require 'proof)

(defvar easycrypt-last-but-one-statenum 0)

(defvar easycrypt-last-but-one-proofdepth 0)
(defvar easycrypt-last-but-one-withproof "T")

; Default prover
(defvar easycrypt-last-but-one-timeout  10)
(defvar easycrypt-last-but-one-tacticnum 0)

;; Function for set or get the information in the span
(defsubst easycrypt-get-span-statenum (span)
  "Return the state number of the SPAN."
  (span-property span 'statenum))

(defsubst easycrypt-get-span-withproof (span)
  "Return the tactic number of the SPAN."
  (span-property span 'withproof))

(defsubst easycrypt-get-span-timeout (span)
  "Return the tactic number of the SPAN."
  (span-property span 'timeout))

(defsubst easycrypt-get-span-tacticnum (span)
  "Return the tactic number of the SPAN."
  (span-property span 'tacticnum))

(defsubst easycrypt-get-span-proofdepth (span)
  "Return the proof depth number of the SPAN."
  (span-property span 'proofdepth))

(defsubst easycrypt-set-span-statenum (span val)
  "Set the state number of the SPAN to VAL."
  (span-set-property span 'statenum val))

(defsubst easycrypt-set-span-withproof (span val)
  "Set the tactic number of the SPAN to VAL."
  (span-set-property span 'withproof val))

(defsubst easycrypt-set-span-timeout (span val)
  "Set the tactic number of the SPAN to VAL."
  (span-set-property span 'timeout val))

(defsubst easycrypt-set-span-tacticnum (span val)
  "Set the tactic number of the SPAN to VAL."
  (span-set-property span 'tacticnum val))

(defsubst easycrypt-set-span-proofdepth (span val)
  "Set the proof depth number of the SPAN to VAL."
  (span-set-property span 'proofdepth val)) 

(defsubst proof-last-locked-span ()
  (with-current-buffer proof-script-buffer
  (span-at (- (proof-unprocessed-begin) 1) 'type)))

;; The prompt format is ....
(defun easycrypt-last-prompt-info (s)
  "Extract the information from de prompt."
  (let ((lastprompt (or s (error "no prompt"))))
	 (when (string-match "\\[\\([0-9]+\\)|\\([0-9]+\\)|\\([TF]\\)|\\([0-9]+\\)|\\([0-9]+\\)]" lastprompt)
		(list (string-to-number (match-string 1 lastprompt)) ; Global state
				(string-to-number (match-string 2 lastprompt)) ; Proof depth 
				(match-string 3 lastprompt) ; Withproof
				(string-to-number (match-string 4 lastprompt)) ; Timeout
				(string-to-number (match-string 5 lastprompt))
				)))) ; Tactic number

(defun easycrypt-last-prompt-info-safe ()
  "Take from `proof-shell-last-prompt' the last information in the prompt."
  (easycrypt-last-prompt-info proof-shell-last-prompt))

(defun easycrypt-set-state-infos ()
  "Set information necessary for backtracking."
  (if proof-shell-last-prompt
	 ;; infos = prompt infos of the very last prompt
	 ;; sp = last locked span, which we want to fill with prompt infos
	 (let ((sp    (if proof-script-buffer (proof-last-locked-span)))
			 (infos (or (easycrypt-last-prompt-info-safe) '(0 0 "T" 3 0  nil))))
		; Global state
		(unless (or (not sp) (easycrypt-get-span-statenum sp))
		  (easycrypt-set-span-statenum sp easycrypt-last-but-one-statenum))
		(setq easycrypt-last-but-one-statenum (car infos))
		; Proof depth 
		(unless (or (not sp) (easycrypt-get-span-proofdepth sp))
		  (easycrypt-set-span-proofdepth sp easycrypt-last-but-one-proofdepth))
		(setq easycrypt-last-but-one-proofdepth (car (cdr infos)))
	   (if (= easycrypt-last-but-one-proofdepth 0) (proof-clean-buffer proof-goals-buffer))
      ; Withproof
      (unless (or (not sp) (easycrypt-get-span-withproof sp))
		  (easycrypt-set-span-withproof sp easycrypt-last-but-one-withproof))
		(setq easycrypt-last-but-one-withproof (car (cdr (cdr infos))))
      ; Timeout
      (unless (or (not sp) (easycrypt-get-span-timeout sp))
		  (easycrypt-set-span-timeout sp easycrypt-last-but-one-timeout))
		(setq easycrypt-last-but-one-timeout (car (cdr (cdr (cdr infos)))))
		; Tactic number
      (unless (or (not sp) (easycrypt-get-span-tacticnum sp))
		  (easycrypt-set-span-tacticnum sp easycrypt-last-but-one-tacticnum))
		(setq easycrypt-last-but-one-tacticnum (car (cdr (cdr (cdr (cdr infos))))))
				)))

(add-hook 'proof-state-change-hook 'easycrypt-set-state-infos)

(defun easycrypt-find-and-forget (span)
  (let  (
			(proofdepth  (easycrypt-get-span-proofdepth span))
			(span-staten (easycrypt-get-span-statenum span))
			(withproof   (easycrypt-get-span-withproof span))
			(timeout     (easycrypt-get-span-timeout span))
			(tacticnum   (easycrypt-get-span-tacticnum span))
			)

	 (if (= proofdepth 0) (proof-clean-buffer proof-goals-buffer))
	 ;(proof-clean-buffer proof-goals-buffer)
	 ;(proof-clean-buffer proof-response-buffer)

	 (list 
		(format "undo %s %s %s %s %s."
				  (int-to-string span-staten)
				  (int-to-string proofdepth)
				  withproof
				  (int-to-string timeout)
				  (int-to-string tacticnum)
				  ;easycrypt-terminal-string
				  ))))


(provide 'easycrypt-hooks)
