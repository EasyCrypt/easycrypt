(require 'proof-unicode-tokens)


(defun certicrypt-unicode-tokens-set (sym val)
  "Change ..."
  (set-default sym val)
  (when (featurep 'certicrypt-unicode-tokens)
    (proof-unicode-tokens-configure)))




(defcustom certicrypt-token-symbol-map
  '(;; Greek letters
    ("alpha" "α")
    ("beta" "β")
    ("gamma" "γ")
    ("delta" "δ")
    ("epsilon" "ε")
    ("zeta" "ζ")
    ("eta" "η")
    ("theta" "θ")
    ("iota" "ι")
    ("kappa" "κ")
    ("lambda" "λ")
    ("mu" "μ")
    ("nu" "ν")
    ("xi" "ξ")
    ("pi" "π")
    ("rho" "ρ")
    ("sigma" "σ")
    ("tau" "τ")
    ("upsilon" "υ")
    ("phi" "ϕ")
    ("chi" "χ")
    ("psi" "ψ")
    ("omega" "ω")
    ("Gamma" "Γ")
    ("Delta" "Δ")
    ("Theta" "Θ")
    ("Lambda" "Λ")
    ("Xi" "Ξ")
    ("Pi" "Π")
    ("Sigma" "Σ")
    ("Upsilon" "Υ")
    ("Phi" "Φ")
    ("Psi" "Ψ")
    ("Omega" "Ω")
 
    ;; logic
    ("forall" "∀")
    ("exists" "∃")
    ("\\/" "∨")
    ("/\\" "∧")
    ("false" "false" bold sans)
    ("true" "true" bold sans)
 
    ;; types
    ("nat" "ℕ" type)
    ("complex" "ℂ" type)
    ("real" "ℝ" type)
    ("int" "ℤ" type)
    ("rat" "ℚ" type)
    ("bool" "B" underline type)
    
    ;; symbols without utf8.v  (but also without context)
    ("lhd" "⊲")
    ("rhd" "⊳")
    ("<=" "≤")
    (">=" "≥")
    ("=>" "⇒")
    ("->" "→")
    ("<-" "←")
    ("<->" "↔")
    ("++" "⧺")
    ("<<" "《")
    (">>" "》")
    ("==>" "⟹") 


    ;; Equivalence
    ;("===" "≡") ; equiv
    ;("=/=" "≢")  ; complement equiv
    ;("=~=" "≅") ; pequiv
    ;("==b" "≡") ; NB: same presentation
    ;("<>b" "≢") ; NB: same presentation
    
    ;; ("==" "≡")  ; Setoid equiv (NB: same presentation, pot confusing)

    ;("-->" "⟹-") ; Morphisms
    ;("++>" "⟹+") ; 
    
    ;(":=" "≔")
    ;("|-" "⊢")
    ;("<>" "≠")
    ;("-|" "⊣")
    
    ;("~"  "¬")
    )
  "Table mapping Coq tokens to Unicode strings"
  :type 'unicode-tokens-token-symbol-map
  :set 'certicrypt-unicode-tokens-set     
  :group 'certicrypt
  :tag "Certicrypt Unicode Token Mapping")
  
  


(defcustom certicrypt-shortcut-alist
  '(; short cut, REAL unicode string
    ;("<>" . "⋄")
    )
  "Shortcut key sequence table for Unicode strings."
  :type '(repeat (cons (string :tag "Shortcut sequence")
    (string :tag "Unicode string")))
  :set 'certicrypt-unicode-tokens-set     
  :group 'certicrypt       
  :tag "Certicrypt Unicode Input Shortcuts")  



(provide 'certicrypt-unicode-tokens)

;;; certicrypt-unicode-tokens.el ends here
