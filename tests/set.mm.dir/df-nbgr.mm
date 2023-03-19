
axiom df-nbgr
  let vv: setvar v
  let ve: setvar e
  let vg: setvar g
  let vn: setvar n
  assert |- NeighbVtx = ( g e. _V , v e. ( Vtx ` g ) |-> { n e. ( ( Vtx ` g ) \ { v } ) | E. e e. ( Edg ` g ) { v , n } C_ e } )
end
