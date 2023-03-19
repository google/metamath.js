
axiom df-subr
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  assert |- -r = ( x e. _V , y e. _V |-> ( v e. RR |-> ( ( x ` v ) - ( y ` v ) ) ) )
end
