include "cms.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "cflim.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "ccfil.mm"
include "wral.mm"
include "cme.mm"
include "iscmet.mm"
include "simprbi.mm"
include "wceq.mm"
include "oveq2.mm"
include "neeq1d.mm"
include "rspccva.mm"
include "sylan.mm"

theorem cmetcvg
  let cD: class D
  let cF: class F
  let cJ: class J
  let cX: class X
  let vd: setvar d
  let vf: setvar f
  let vx: setvar x
  assume iscmet.1: |- J = ( MetOpen ` D )


  assert |- ( ( D e. ( CMet ` X ) /\ F e. ( CauFil ` D ) ) -> ( J fLim F ) =/= (/) )

  proof
    cD
    cX
    cms
    cfv
    wcel
    #
    cJ
    vf
    cv
    #
    cflim
    co
    #
    c0
    wne
    #
    vf
    cD
    ccfil
    cfv
    #
    wral
    #
    cF
    @4
    wcel
    cJ
    cF
    cflim
    co
    #
    c0
    wne
    #
    @0
    cD
    cX
    cme
    cfv
    wcel
    @5
    cD
    vf
    cJ
    cX
    iscmet.1
    iscmet
    simprbi
    @3
    @7
    vf
    cF
    @4
    @1
    cF
    wceq
    @2
    @6
    c0
    @1
    cF
    cJ
    cflim
    oveq2
    neeq1d
    rspccva
    sylan
end
