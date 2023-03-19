include "ax-9.mm"

theorem ax9v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x y
  assert |- ( x = y -> ( z e. x -> z e. y ) )

  proof
    vx
    vy
    vz
    ax-9
end
