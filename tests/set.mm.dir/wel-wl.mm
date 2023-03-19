include "cv.mm"
include "wcel-wl.mm"

theorem wel-wl
  let vx: setvar x
  let vy: setvar y


  assert wff x wl-el y

  proof
    vx
    vy
    cv
    wcel-wl
end
