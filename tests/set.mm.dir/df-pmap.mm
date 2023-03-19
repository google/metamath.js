
axiom df-pmap
  let vk: setvar k
  let vp: setvar p
  let va: setvar a
  assert |- pmap = ( k e. _V |-> ( a e. ( Base ` k ) |-> { p e. ( Atoms ` k ) | p ( le ` k ) a } ) )
end
