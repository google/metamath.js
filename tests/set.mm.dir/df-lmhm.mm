
axiom df-lmhm
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vt: setvar t
  let vf: setvar f
  let vs: setvar s
  assert |- LMHom = ( s e. LMod , t e. LMod |-> { f e. ( s GrpHom t ) | [. ( Scalar ` s ) / w ]. ( ( Scalar ` t ) = w /\ A. x e. ( Base ` w ) A. y e. ( Base ` s ) ( f ` ( x ( .s ` s ) y ) ) = ( x ( .s ` t ) ( f ` y ) ) ) } )
end
