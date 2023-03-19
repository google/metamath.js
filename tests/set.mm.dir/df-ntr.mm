
axiom df-ntr
  let vx: setvar x
  let vj: setvar j
  assert |- int = ( j e. Top |-> ( x e. ~P U. j |-> U. ( j i^i ~P x ) ) )
end
