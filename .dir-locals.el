((tuareg-mode .
   ((require-final-newline . t)
    (c-basic-offset . 2)
    (tab-width . 2)
    (indent-tabs-mode . nil)
    (eval . (add-hook 'write-contents-functions 'delete-trailing-whitespace))))
 (easycrypt-mode .
   ((require-final-newline . t)
    (indent-tabs-mode . nil)
    (eval . (add-hook 'write-contents-functions 'delete-trailing-whitespace)))))
