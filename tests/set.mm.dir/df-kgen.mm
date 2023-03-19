
axiom df-kgen
  let vx: setvar x
  let vj: setvar j
  let vk: setvar k
  assert |- kGen = ( j e. Top |-> { x e. ~P U. j | A. k e. ~P U. j ( ( j |`t k ) e. Comp -> ( x i^i k ) e. ( j |`t k ) ) } )
end
