
axiom df-rprm
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vp: setvar p
  let vb: setvar b
  let vd: setvar d
  assert |- RPrime = ( w e. _V |-> [_ ( Base ` w ) / b ]_ { p e. ( b \ ( ( Unit ` w ) u. { ( 0g ` w ) } ) ) | A. x e. b A. y e. b [. ( ||r ` w ) / d ]. ( p d ( x ( .r ` w ) y ) -> ( p d x \/ p d y ) ) } )
end
