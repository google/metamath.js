
axiom ax-9
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assert |- ( x = y -> ( z e. x -> z e. y ) )
end
