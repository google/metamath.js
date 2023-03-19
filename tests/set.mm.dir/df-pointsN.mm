
axiom df-pointsN
  let vk: setvar k
  let vq: setvar q
  let vp: setvar p
  assert |- Points = ( k e. _V |-> { q | E. p e. ( Atoms ` k ) q = { p } } )
end
