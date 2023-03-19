include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "vprc.mm"
include "isset.mm"
include "mtbi.mm"

theorem vnex
  let vx: setvar x


  assert |- -. E. x x = _V

  proof
    cvv
    cvv
    wcel
    vx
    cv
    cvv
    wceq
    vx
    wex
    vprc
    vx
    cvv
    isset
    mtbi
end
