include "cfv.mm"
include "cv.mm"
include "wbr.mm"
include "cio.mm"
include "cvv.mm"
include "df-fv.mm"
include "iotaex.mm"
include "eqeltri.mm"

theorem fvex
  let cA: class A
  let cF: class F
  let vx: setvar x


  assert |- ( F ` A ) e. _V

  proof
    cA
    cF
    cfv
    cA
    vx
    cv
    cF
    wbr
    #
    vx
    cio
    cvv
    vx
    cA
    cF
    df-fv
    @0
    vx
    iotaex
    eqeltri
end
