

axiom ax-13
  param vx: setvar x
  param vy: setvar y
  param vz: setvar z
  assert |- ( -. x = y -> ( y = z -> A. x y = z ) )
end
