
axiom ax-wl-13v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assert |- ( -. A. x x = y -> ( y = z -> A. x y = z ) )
end
