include "ax9v.mm"

theorem ax9v1
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x y
  disjoint x z
  assert |- ( x = y -> ( z e. x -> z e. y ) )

  proof
    vx
    vy
    vz
    ax9v
end
