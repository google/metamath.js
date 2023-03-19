
axiom df-cls
  let vx: setvar x
  let vy: setvar y
  let vj: setvar j
  assert |- cls = ( j e. Top |-> ( x e. ~P U. j |-> |^| { y e. ( Clsd ` j ) | x C_ y } ) )
end
