
axiom df-fl
  let vx: setvar x
  let vy: setvar y
  assert |- |_ = ( x e. RR |-> ( iota_ y e. ZZ ( y <_ x /\ x < ( y + 1 ) ) ) )
end
