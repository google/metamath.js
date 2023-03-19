

axiom ax-ext
  param vx: setvar x
  param vy: setvar y
  param vz: setvar z
  assert |- ( A. z ( z e. x <-> z e. y ) -> x = y )
end
