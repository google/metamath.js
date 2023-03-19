include "ax-13.mm"

theorem ax13v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x z
  disjoint y z
  assert |- ( -. x = y -> ( y = z -> A. x y = z ) )

  proof
    vx
    vy
    vz
    ax-13
end
