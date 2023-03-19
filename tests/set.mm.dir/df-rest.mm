
axiom df-rest
  let vx: setvar x
  let vy: setvar y
  let vj: setvar j
  assert |- |`t = ( j e. _V , x e. _V |-> ran ( y e. j |-> ( y i^i x ) ) )
end
