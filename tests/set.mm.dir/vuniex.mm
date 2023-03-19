include "cv.mm"
include "vex.mm"
include "uniex.mm"

theorem vuniex
  let vx: setvar x


  assert |- U. x e. _V

  proof
    vx
    cv
    vx
    vex
    uniex
end
