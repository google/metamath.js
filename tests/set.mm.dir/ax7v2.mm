include "ax7v.mm"

theorem ax7v2
  param vx: setvar x
  param vy: setvar y
  param vz: setvar z

  disjoint x y
  disjoint y z
  assert |- ( x = y -> ( x = z -> y = z ) )

  proof
    vx
    vy
    vz
    ax7v
end
