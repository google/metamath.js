
axiom df-nmo
  let vx: setvar x
  let vt: setvar t
  let vf: setvar f
  let vs: setvar s
  let vr: setvar r
  assert |- normOp = ( s e. NrmGrp , t e. NrmGrp |-> ( f e. ( s GrpHom t ) |-> inf ( { r e. ( 0 [,) +oo ) | A. x e. ( Base ` s ) ( ( norm ` t ) ` ( f ` x ) ) <_ ( r x. ( ( norm ` s ) ` x ) ) } , RR* , < ) ) )
end
