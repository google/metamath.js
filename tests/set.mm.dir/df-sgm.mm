
axiom df-sgm
  let vx: setvar x
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p
  assert |- sigma = ( x e. CC , n e. NN |-> sum_ k e. { p e. NN | p || n } ( k ^c x ) )
end
