
axiom ax-cc
  let vx: setvar x
  let vz: setvar z
  let vf: setvar f
  assert |- ( x ~~ _om -> E. f A. z e. x ( z =/= (/) -> ( f ` z ) e. z ) )
end
