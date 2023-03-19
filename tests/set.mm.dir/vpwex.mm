include "cv.mm"
include "vex.mm"
include "pwex.mm"

theorem vpwex
  let vx: setvar x


  assert |- ~P x e. _V

  proof
    vx
    cv
    vx
    vex
    pwex
end
