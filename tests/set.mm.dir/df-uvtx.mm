
axiom df-uvtx
  let vv: setvar v
  let vg: setvar g
  let vn: setvar n
  assert |- UnivVtx = ( g e. _V |-> { v e. ( Vtx ` g ) | A. n e. ( ( Vtx ` g ) \ { v } ) n e. ( g NeighbVtx v ) } )
end
