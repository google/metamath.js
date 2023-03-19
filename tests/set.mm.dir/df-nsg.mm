
axiom df-nsg
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vs: setvar s
  let vp: setvar p
  let vb: setvar b
  assert |- NrmSGrp = ( w e. Grp |-> { s e. ( SubGrp ` w ) | [. ( Base ` w ) / b ]. [. ( +g ` w ) / p ]. A. x e. b A. y e. b ( ( x p y ) e. s <-> ( y p x ) e. s ) } )
end
