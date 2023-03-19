include "cv.mm"
include "vex.mm"
include "snid.mm"

theorem vsnid
  let vx: setvar x


  assert |- x e. { x }

  proof
    vx
    cv
    vx
    vex
    snid
end
