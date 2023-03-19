
axiom df-pfx
  let vs: setvar s
  let vl: setvar l
  assert |- prefix = ( s e. _V , l e. NN0 |-> ( s substr <. 0 , l >. ) )
end
