
axiom df-vtx
  let vg: setvar g
  assert |- Vtx = ( g e. _V |-> if ( g e. ( _V X. _V ) , ( 1st ` g ) , ( Base ` g ) ) )
end
