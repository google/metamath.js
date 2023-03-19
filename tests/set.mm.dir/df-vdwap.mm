
axiom df-vdwap
  let vk: setvar k
  let vm: setvar m
  let va: setvar a
  let vd: setvar d
  assert |- AP = ( k e. NN0 |-> ( a e. NN , d e. NN |-> ran ( m e. ( 0 ... ( k - 1 ) ) |-> ( a + ( m x. d ) ) ) ) )
end
