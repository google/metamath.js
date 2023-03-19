
axiom ax-c14
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assert |- ( -. A. z z = x -> ( -. A. z z = y -> ( x e. y -> A. z x e. y ) ) )
end
