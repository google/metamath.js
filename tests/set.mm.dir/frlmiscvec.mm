include "cnzr.mm"
include "wcel.mm"
include "c0.mm"
include "csn.mm"
include "cxp.mm"
include "cen.mm"
include "wbr.mm"
include "cfrlm.mm"
include "co.mm"
include "clmic.mm"
include "wa.mm"
include "cvv.mm"
include "simpr.mm"
include "0ex.mm"
include "xpsneng.mm"
include "ensymd.mm"
include "sylancl.mm"
include "frlmisfrlm.mm"
include "mpd3an3.mm"

theorem frlmiscvec
  let cR: class R
  let cI: class I
  let cY: class Y


  assert |- ( ( R e. NzRing /\ I e. Y ) -> ( R freeLMod I ) ~=m ( R freeLMod ( I X. { (/) } ) ) )

  proof
    cR
    cnzr
    wcel
    #
    cI
    cY
    wcel
    #
    cI
    cI
    c0
    csn
    cxp
    #
    cen
    wbr
    #
    cR
    cI
    cfrlm
    co
    cR
    @2
    cfrlm
    co
    clmic
    wbr
    @0
    @1
    wa
    @1
    c0
    cvv
    wcel
    #
    @3
    @0
    @1
    simpr
    0ex
    @1
    @4
    wa
    @2
    cI
    cI
    c0
    cY
    cvv
    xpsneng
    ensymd
    sylancl
    cR
    cI
    @2
    cY
    frlmisfrlm
    mpd3an3
end
