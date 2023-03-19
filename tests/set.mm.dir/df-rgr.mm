
axiom df-rgr
  let vv: setvar v
  let vg: setvar g
  let vk: setvar k
  assert |- RegGraph = { <. g , k >. | ( k e. NN0* /\ A. v e. ( Vtx ` g ) ( ( VtxDeg ` g ) ` v ) = k ) }
end
