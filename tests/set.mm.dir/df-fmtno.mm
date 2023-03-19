
axiom df-fmtno
  let vn: setvar n
  assert |- FermatNo = ( n e. NN0 |-> ( ( 2 ^ ( 2 ^ n ) ) + 1 ) )
end
