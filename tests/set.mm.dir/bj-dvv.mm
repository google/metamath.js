include "bj-hbaeb2.mm"

theorem bj-dvv
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x x = y <-> A. x A. y x = y )

  proof
    vx
    vy
    vy
    bj-hbaeb2
end
