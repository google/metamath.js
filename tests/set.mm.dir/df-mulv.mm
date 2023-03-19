
axiom df-mulv
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  assert |- .v = ( x e. _V , y e. _V |-> ( v e. RR |-> ( x x. ( y ` v ) ) ) )
end
