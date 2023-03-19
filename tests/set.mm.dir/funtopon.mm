include "cvv.mm"
include "cv.mm"
include "cuni.mm"
include "wceq.mm"
include "ctop.mm"
include "crab.mm"
include "ctopon.mm"
include "df-topon.mm"
include "funmpt2.mm"

theorem funtopon
  let vx: setvar x
  let vy: setvar y


  assert |- Fun TopOn

  proof
    vy
    cvv
    vy
    cv
    vx
    cv
    cuni
    wceq
    vx
    ctop
    crab
    ctopon
    vx
    vy
    df-topon
    funmpt2
end
