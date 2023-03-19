include "axc11n.mm"

theorem axi10
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x x = y -> A. y y = x )

  proof
    vx
    vy
    axc11n
end
