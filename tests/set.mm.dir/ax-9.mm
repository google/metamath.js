

axiom ax-9
  param vx: setvar x
  param vy: setvar y
  param vz: setvar z
  assert |- ( x = y -> ( z e. x -> z e. y ) )
end
