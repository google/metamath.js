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
include "ctermo.mm"
include "df-termo.mm"
include "mptrcl.mm"

theorem termorcl
  let cC: class C
  let cT: class T
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vh: setvar h


  assert |- ( T e. ( TermO ` C ) -> C e. Cat )

  proof
    vc
    ccat
    vh
    cv
    vb
    cv
    va
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
    ctermo
    cT
    cC
    vh
    va
    vb
    vc
    df-termo
    mptrcl
end
