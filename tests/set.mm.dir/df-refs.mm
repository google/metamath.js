
axiom df-refs
  let vx: setvar x
  assert |- Refs = { x | ( _I i^i ( dom x X. ran x ) ) _S ( x i^i ( dom x X. ran x ) ) }
end
