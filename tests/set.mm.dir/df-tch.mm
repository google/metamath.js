
axiom df-tch
  let vx: setvar x
  let vw: setvar w
  assert |- toCHil = ( w e. _V |-> ( w toNrmGrp ( x e. ( Base ` w ) |-> ( sqrt ` ( x ( .i ` w ) x ) ) ) ) )
end
