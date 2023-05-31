include "ax-13.mm"

theorem ax13v
  param vx: setvar x
  param vy: setvar y
  param vz: setvar z

  disjoint x z
  disjoint y z
  assert |- ( -. x = y -> ( y = z -> A. x y = z ) )

  proof
    vx
    vy
    vz
    ax-13
end
