
axiom df-cgrg
  let vg: setvar g
  let vi: setvar i
  let vj: setvar j
  let va: setvar a
  let vb: setvar b
  assert |- cgrG = ( g e. _V |-> { <. a , b >. | ( ( a e. ( ( Base ` g ) ^pm RR ) /\ b e. ( ( Base ` g ) ^pm RR ) ) /\ ( dom a = dom b /\ A. i e. dom a A. j e. dom a ( ( a ` i ) ( dist ` g ) ( a ` j ) ) = ( ( b ` i ) ( dist ` g ) ( b ` j ) ) ) ) } )
end
