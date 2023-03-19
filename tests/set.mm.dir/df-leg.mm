
axiom df-leg
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let vp: setvar p
  let vd: setvar d
  assert |- leG = ( g e. _V |-> { <. e , f >. | [. ( Base ` g ) / p ]. [. ( dist ` g ) / d ]. [. ( Itv ` g ) / i ]. E. x e. p E. y e. p ( f = ( x d y ) /\ E. z e. p ( z e. ( x i y ) /\ e = ( x d z ) ) ) } )
end
