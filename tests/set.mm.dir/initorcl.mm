include "ccat.mm"
include "cv.mm"
include "chom.mm"
include "cfv.mm"
include "co.mm"
include "wcel.mm"
include "weu.mm"
include "cbs.mm"
include "wral.mm"
include "crab.mm"
include "cinito.mm"
include "df-inito.mm"
include "mptrcl.mm"

theorem initorcl
  let cC: class C
  let cI: class I
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vh: setvar h


  assert |- ( I e. ( InitO ` C ) -> C e. Cat )

  proof
    vc
    ccat
    vh
    cv
    va
    cv
    vb
    cv
    vc
    cv
    #
    chom
    cfv
    co
    wcel
    vh
    weu
    vb
    @0
    cbs
    cfv
    #
    wral
    va
    @1
    crab
    cinito
    cI
    cC
    vh
    va
    vb
    vc
    df-inito
    mptrcl
end
