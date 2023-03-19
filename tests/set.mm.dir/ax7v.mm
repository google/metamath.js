include "ax-7.mm"

theorem ax7v
  param vx: setvar x
  param vy: setvar y
  param vz: setvar z

  disjoint x y
  assert |- ( x = y -> ( x = z -> y = z ) )

  proof
    vx
    vy
    vz
    ax-7
end
