
axiom df-clwwlkn
  let vw: setvar w
  let vg: setvar g
  let vn: setvar n
  assert |- ClWWalksN = ( n e. NN0 , g e. _V |-> { w e. ( ClWWalks ` g ) | ( # ` w ) = n } )
end
