
axiom df-phl
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  assert |- PreHil = { g e. LVec | [. ( Base ` g ) / v ]. [. ( .i ` g ) / h ]. [. ( Scalar ` g ) / f ]. ( f e. *Ring /\ A. x e. v ( ( y e. v |-> ( y h x ) ) e. ( g LMHom ( ringLMod ` f ) ) /\ ( ( x h x ) = ( 0g ` f ) -> x = ( 0g ` g ) ) /\ A. y e. v ( ( *r ` f ) ` ( x h y ) ) = ( y h x ) ) ) }
end
