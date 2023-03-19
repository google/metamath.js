
axiom df-kq
  let vx: setvar x
  let vy: setvar y
  let vj: setvar j
  assert |- KQ = ( j e. Top |-> ( j qTop ( x e. U. j |-> { y e. j | x e. y } ) ) )
end
