

axiom ax-7
  param vx: setvar x
  param vy: setvar y
  param vz: setvar z
  assert |- ( x = y -> ( x = z -> y = z ) )
end
