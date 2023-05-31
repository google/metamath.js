include "cv.mm"
include "wcel.mm"

theorem wel
  param vx: setvar x
  param vy: setvar y


  assert wff x e. y

  proof
    vx
    cv
    vy
    cv
    wcel
end
