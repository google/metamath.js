
axiom ax-8d
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assert |- ( x = y -> ( x = z -> y = z ) )
end
