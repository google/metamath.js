
axiom df-mid
  let vg: setvar g
  let vm: setvar m
  let va: setvar a
  let vb: setvar b
  assert |- midG = ( g e. _V |-> ( a e. ( Base ` g ) , b e. ( Base ` g ) |-> ( iota_ m e. ( Base ` g ) b = ( ( ( pInvG ` g ) ` m ) ` a ) ) ) )
end
