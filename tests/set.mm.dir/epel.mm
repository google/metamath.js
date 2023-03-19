include "cv.mm"
include "vex.mm"
include "epelc.mm"

theorem epel
  let vx: setvar x
  let vy: setvar y


  assert |- ( x _E y <-> x e. y )

  proof
    vx
    cv
    vy
    cv
    vy
    vex
    epelc
end
