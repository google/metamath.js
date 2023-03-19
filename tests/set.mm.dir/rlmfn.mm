include "cvv.mm"
include "cv.mm"
include "cbs.mm"
include "cfv.mm"
include "csra.mm"
include "crglmod.mm"
include "fvex.mm"
include "df-rgmod.mm"
include "fnmpti.mm"

theorem rlmfn
  let cW: class W
  let va: setvar a


  assert |- ringLMod Fn _V

  proof
    va
    cvv
    va
    cv
    #
    cbs
    cfv
    #
    @0
    csra
    cfv
    #
    cfv
    crglmod
    @1
    @2
    fvex
    va
    df-rgmod
    fnmpti
end
