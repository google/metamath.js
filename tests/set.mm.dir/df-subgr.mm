
axiom df-subgr
  let vg: setvar g
  let vs: setvar s
  assert |- SubGraph = { <. s , g >. | ( ( Vtx ` s ) C_ ( Vtx ` g ) /\ ( iEdg ` s ) = ( ( iEdg ` g ) |` dom ( iEdg ` s ) ) /\ ( Edg ` s ) C_ ~P ( Vtx ` s ) ) }
end
