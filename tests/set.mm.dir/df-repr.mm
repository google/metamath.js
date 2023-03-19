
axiom df-repr
  let vm: setvar m
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assert |- repr = ( s e. NN0 |-> ( b e. ~P NN , m e. ZZ |-> { c e. ( b ^m ( 0 ..^ s ) ) | sum_ a e. ( 0 ..^ s ) ( c ` a ) = m } ) )
end
