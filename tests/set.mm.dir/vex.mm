include "cv.mm"
include "cvv.mm"
include "wcel.mm"
include "weq.mm"
include "equid.mm"
include "df-v.mm"
include "abeq2i.mm"
include "mpbir.mm"

theorem vex
  let vx: setvar x


  assert |- x e. _V

  proof
    vx
    cv
    cvv
    wcel
    vx
    vx
    weq
    #
    vx
    equid
    @0
    vx
    cvv
    vx
    df-v
    abeq2i
    mpbir
end
