
axiom df-ascl
  let vx: setvar x
  let vw: setvar w
  assert |- algSc = ( w e. _V |-> ( x e. ( Base ` ( Scalar ` w ) ) |-> ( x ( .s ` w ) ( 1r ` w ) ) ) )
end
