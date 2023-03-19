include "ax-9.mm"

theorem ax9v
  param vx: setvar x
  param vy: setvar y
  param vz: setvar z

  disjoint x y
  assert |- ( x = y -> ( z e. x -> z e. y ) )

  proof
    vx
    vy
    vz
    ax-9
end
