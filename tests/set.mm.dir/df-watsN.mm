
axiom df-watsN
  let vk: setvar k
  let vd: setvar d
  assert |- WAtoms = ( k e. _V |-> ( d e. ( Atoms ` k ) |-> ( ( Atoms ` k ) \ ( ( _|_P ` k ) ` { d } ) ) ) )
end
