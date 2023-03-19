
axiom df-clwwlknOLD
  let vw: setvar w
  let vg: setvar g
  let vn: setvar n
  assert |- ClWWalksNOLD = ( n e. NN , g e. _V |-> { w e. ( ClWWalks ` g ) | ( # ` w ) = n } )
end
