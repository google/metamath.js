
axiom ax-ext
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assert |- ( A. z ( z e. x <-> z e. y ) -> x = y )
end
