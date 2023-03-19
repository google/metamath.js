
axiom df-cplgr
  let vg: setvar g
  assert |- ComplGraph = { g | ( UnivVtx ` g ) = ( Vtx ` g ) }
end
