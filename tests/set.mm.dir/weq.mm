include "cv.mm"
include "wceq.mm"

theorem weq
  param vx: setvar x
  param vy: setvar y


  assert wff x = y

  proof
    vx
    cv
    vy
    cv
    wceq
end
