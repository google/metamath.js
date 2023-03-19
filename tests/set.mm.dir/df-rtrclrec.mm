
axiom df-rtrclrec
  let vn: setvar n
  let vr: setvar r
  assert |- t*rec = ( r e. _V |-> U_ n e. NN0 ( r ^r n ) )
end
