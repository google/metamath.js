include "ax7v.mm"

theorem ax7v1
  param vx: setvar x
  param vy: setvar y
  param vz: setvar z

  disjoint x y
  disjoint x z
  assert |- ( x = y -> ( x = z -> y = z ) )

  proof
    vx
    vy
    vz
    ax7v
end
