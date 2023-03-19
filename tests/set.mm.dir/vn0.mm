include "cv.mm"
include "cvv.mm"
include "vex.mm"
include "ne0ii.mm"

theorem vn0
  let vx: setvar x


  assert |- _V =/= (/)

  proof
    vx
    cv
    cvv
    vx
    vex
    ne0ii
end
