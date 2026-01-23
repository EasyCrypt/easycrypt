 # Features (for now) #
 
- new keyords qmodule, qproc and qvar (done)
- only instances of qvars are locally in qrocs (for now) (done)
- qprocs only have deterministic instructions (done?)
- qprocs are not inlineable (done?)
- only instances of qmodules are abstract (quantum) adversaries (done?)
- qprocs can not be accessed by classical adversaries
- only rule that can be applied to quantum adversaries is of the type:

$$ \frac{U_f = U_{g}}{ \\{ qstate_{A_l}^i = qstate_{A_r}^i \\} \ A_l^{U_f} \sim A_r^{U_{g}} \ \\{ qstate_{A_l}^f = qstate_{A_r}^f \\} } $$
