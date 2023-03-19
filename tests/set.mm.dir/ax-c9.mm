
axiom ax-c9
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assert |- ( -. A. z z = x -> ( -. A. z z = y -> ( x = y -> A. z x = y ) ) )
end
