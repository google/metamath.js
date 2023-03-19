
axiom df-cnvrefs
  let vx: setvar x
  assert |- CnvRefs = { x | ( _I i^i ( dom x X. ran x ) ) `' _S ( x i^i ( dom x X. ran x ) ) }
end
