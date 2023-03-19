include "aevlem.mm"

theorem bj-axc11nv
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- ( A. x x = y -> A. y y = x )

  proof
    vx
    vy
    vy
    vx
    aevlem
end
