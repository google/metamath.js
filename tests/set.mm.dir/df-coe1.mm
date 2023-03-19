
axiom df-coe1
  let vf: setvar f
  let vn: setvar n
  assert |- coe1 = ( f e. _V |-> ( n e. NN0 |-> ( f ` ( 1o X. { n } ) ) ) )
end
