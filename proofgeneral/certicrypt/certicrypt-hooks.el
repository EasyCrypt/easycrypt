(require 'span)
(require 'proof)
;(require 'certicrypt-syntax)

(defvar certicrypt-last-but-one-statenum 0)

(defvar certicrypt-last-but-one-proofdepth 0)
(defvar certicrypt-last-but-one-withproof "T")

; Default prover
(defvar certicrypt-last-but-one-timeout  10)
(defvar certicrypt-last-but-one-tacticnum 0)


;; Function for set or get the information in the span

(defsubst certicrypt-get-span-statenum (span)
  "Return the state number of the SPAN."
  (span-property span 'statenum))

(defsubst certicrypt-get-span-withproof (span)
  "Return the tactic number of the SPAN."
  (span-property span 'withproof))

(defsubst certicrypt-get-span-timeout (span)
  "Return the tactic number of the SPAN."
  (span-property span 'timeout))

(defsubst certicrypt-get-span-tacticnum (span)
  "Return the tactic number of the SPAN."
  (span-property span 'tacticnum))

(defsubst certicrypt-get-span-proofdepth (span)
  "Return the proof depth number of the SPAN."
  (span-property span 'proofdepth))


(defsubst certicrypt-set-span-statenum (span val)
  "Set the state number of the SPAN to VAL."
  (span-set-property span 'statenum val))

(defsubst certicrypt-set-span-withproof (span val)
  "Set the tactic number of the SPAN to VAL."
  (span-set-property span 'withproof val))

(defsubst certicrypt-set-span-timeout (span val)
  "Set the tactic number of the SPAN to VAL."
  (span-set-property span 'timeout val))

(defsubst certicrypt-set-span-tacticnum (span val)
  "Set the tactic number of the SPAN to VAL."
  (span-set-property span 'tacticnum val))

(defsubst certicrypt-set-span-proofdepth (span val)
  "Set the proof depth number of the SPAN to VAL."
  (span-set-property span 'proofdepth val)) 

(defsubst proof-last-locked-span ()
  (with-current-buffer proof-script-buffer
  (span-at (- (proof-unprocessed-begin) 1) 'type)))



;; The prompt format is ....
(defun certicrypt-last-prompt-info (s)
  "Extract the information from de prompt."
  (let ((lastprompt (or s (error "no prompt"))))
	 (when (string-match "\\[\\([0-9]+\\)|\\([0-9]+\\)|\\([TF]\\)|\\([0-9]+\\)|\\([0-9]+\\)]" lastprompt)
		(list (string-to-number (match-string 1 lastprompt)) ; Global state
				(string-to-number (match-string 2 lastprompt)) ; Proof depth 
				(match-string 3 lastprompt) ; Withproof
				(string-to-number (match-string 4 lastprompt)) ; Timeout
				(string-to-number (match-string 5 lastprompt))
				)))) ; Tactic number

(defun certicrypt-last-prompt-info-safe ()
  "Take from `proof-shell-last-prompt' the last information in the prompt."
  (certicrypt-last-prompt-info proof-shell-last-prompt))



(defun certicrypt-set-state-infos ()
  "Set information necessary for backtracking."
  (if proof-shell-last-prompt
	 ;; infos = prompt infos of the very last prompt
	 ;; sp = last locked span, which we want to fill with prompt infos
	 (let ((sp    (if proof-script-buffer (proof-last-locked-span)))
			 (infos (or (certicrypt-last-prompt-info-safe) '(0 0 "T" 3 0  nil))))
		; Global state
		(unless (or (not sp) (certicrypt-get-span-statenum sp))
		  (certicrypt-set-span-statenum sp certicrypt-last-but-one-statenum))
		(setq certicrypt-last-but-one-statenum (car infos))
		; Proof depth 
		(unless (or (not sp) (certicrypt-get-span-proofdepth sp))
		  (certicrypt-set-span-proofdepth sp certicrypt-last-but-one-proofdepth))
		(setq certicrypt-last-but-one-proofdepth (car (cdr infos)))
	   (if (= certicrypt-last-but-one-proofdepth 0) (proof-clean-buffer proof-goals-buffer))
      ; Withproof
      (unless (or (not sp) (certicrypt-get-span-withproof sp))
		  (certicrypt-set-span-withproof sp certicrypt-last-but-one-withproof))
		(setq certicrypt-last-but-one-withproof (car (cdr (cdr infos))))
      ; Timeout
      (unless (or (not sp) (certicrypt-get-span-timeout sp))
		  (certicrypt-set-span-timeout sp certicrypt-last-but-one-timeout))
		(setq certicrypt-last-but-one-timeout (car (cdr (cdr (cdr infos)))))
		; Tactic number
      (unless (or (not sp) (certicrypt-get-span-tacticnum sp))
		  (certicrypt-set-span-tacticnum sp certicrypt-last-but-one-tacticnum))
		(setq certicrypt-last-but-one-tacticnum (car (cdr (cdr (cdr (cdr infos))))))
				)))


(add-hook 'proof-state-change-hook 'certicrypt-set-state-infos)

(defun certicrypt-find-and-forget (span)
  (let  (
			(proofdepth  (certicrypt-get-span-proofdepth span))
			(span-staten (certicrypt-get-span-statenum span))
			(withproof   (certicrypt-get-span-withproof span))
			(timeout     (certicrypt-get-span-timeout span))
			(tacticnum   (certicrypt-get-span-tacticnum span))
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
				  ;certicrypt-terminal-string
				  ))))


(provide 'certicrypt-hooks)

