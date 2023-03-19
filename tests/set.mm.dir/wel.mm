include "cv.mm"
include "wcel.mm"

theorem wel
  let vx: setvar x
  let vy: setvar y


  assert wff x e. y

  proof
    vx
    cv
    vy
    cv
    wcel
end
