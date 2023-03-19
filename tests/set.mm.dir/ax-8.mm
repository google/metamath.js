
axiom ax-8
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assert |- ( x = y -> ( x e. z -> y e. z ) )
end
