
axiom df-reps
  let vx: setvar x
  let vn: setvar n
  let vs: setvar s
  assert |- repeatS = ( s e. _V , n e. NN0 |-> ( x e. ( 0 ..^ n ) |-> s ) )
end
