
axiom df-ef
  let vx: setvar x
  let vk: setvar k
  assert |- exp = ( x e. CC |-> sum_ k e. NN0 ( ( x ^ k ) / ( ! ` k ) ) )
end
