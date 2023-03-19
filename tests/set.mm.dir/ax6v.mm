include "ax-6.mm"

theorem ax6v
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- -. A. x -. x = y

  proof
    vx
    vy
    ax-6
end
