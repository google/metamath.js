include "cv.mm"
include "wceq.mm"

theorem weq
  let vx: setvar x
  let vy: setvar y


  assert wff x = y

  proof
    vx
    cv
    vy
    cv
    wceq
end
