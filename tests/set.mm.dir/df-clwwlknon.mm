
axiom df-clwwlknon
  let vw: setvar w
  let vv: setvar v
  let vg: setvar g
  let vn: setvar n
  assert |- ClWWalksNOn = ( g e. _V |-> ( v e. ( Vtx ` g ) , n e. NN0 |-> { w e. ( n ClWWalksN g ) | ( w ` 0 ) = v } ) )
end
