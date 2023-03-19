include "cv.mm"
include "wcel2-wl.mm"

theorem wel2-wl
  let vx: setvar x
  let vy: setvar y


  assert wff x wl-el2 y

  proof
    vx
    vy
    cv
    wcel2-wl
end
