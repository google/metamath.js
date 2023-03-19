
axiom df-bl
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vd: setvar d
  assert |- ball = ( d e. _V |-> ( x e. dom dom d , z e. RR* |-> { y e. dom dom d | ( x d y ) < z } ) )
end
