
axiom df-mir
  let vg: setvar g
  let vm: setvar m
  let va: setvar a
  let vb: setvar b
  assert |- pInvG = ( g e. _V |-> ( m e. ( Base ` g ) |-> ( a e. ( Base ` g ) |-> ( iota_ b e. ( Base ` g ) ( ( m ( dist ` g ) b ) = ( m ( dist ` g ) a ) /\ m e. ( b ( Itv ` g ) a ) ) ) ) ) )
end
