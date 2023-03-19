include "ax6e.mm"

theorem axi9
  let vx: setvar x
  let vy: setvar y


  assert |- E. x x = y

  proof
    vx
    vy
    ax6e
end
