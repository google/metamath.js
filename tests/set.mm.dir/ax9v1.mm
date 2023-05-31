include "ax9v.mm"

theorem ax9v1
  param vx: setvar x
  param vy: setvar y
  param vz: setvar z

  disjoint x y
  disjoint x z
  assert |- ( x = y -> ( z e. x -> z e. y ) )

  proof
    vx
    vy
    vz
    ax9v
end
