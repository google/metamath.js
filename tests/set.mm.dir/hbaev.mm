include "hbaevg.mm"

theorem hbaev
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x y
  assert |- ( A. x x = y -> A. z A. x x = y )

  proof
    vx
    vy
    vz
    vy
    vx
    hbaevg
end
