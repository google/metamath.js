include "wcel.mm"
include "ccom.mm"
include "wss.mm"
include "wa.mm"
include "ctcl.mm"
include "cfv.mm"
include "cv.mm"
include "cab.mm"
include "cint.mm"
include "wceq.mm"
include "trclfv.mm"
include "adantr.mm"
include "simpr.mm"
include "ssid.mm"
include "jctil.mm"
include "wb.mm"
include "trcleq2lem.mm"
include "elabg.mm"
include "mpbird.mm"
include "intss1.mm"
include "syl.mm"
include "eqsstrd.mm"
include "trclfvlb.mm"
include "eqssd.mm"

theorem cotrtrclfv
  let cR: class R
  let cV: class V
  let vr: setvar r


  assert |- ( ( R e. V /\ ( R o. R ) C_ R ) -> ( t+ ` R ) = R )

  proof
    cR
    cV
    wcel
    #
    cR
    cR
    ccom
    cR
    wss
    #
    wa
    #
    cR
    ctcl
    cfv
    #
    cR
    @2
    @3
    cR
    vr
    cv
    #
    wss
    @4
    @4
    ccom
    @4
    wss
    wa
    #
    vr
    cab
    #
    cint
    #
    cR
    @0
    @3
    @7
    wceq
    @1
    vr
    cR
    cV
    trclfv
    adantr
    @2
    cR
    @6
    wcel
    #
    @7
    cR
    wss
    @2
    @8
    cR
    cR
    wss
    #
    @1
    wa
    #
    @2
    @1
    @9
    @0
    @1
    simpr
    cR
    ssid
    jctil
    @0
    @8
    @10
    wb
    @1
    @5
    @10
    vr
    cR
    cV
    @4
    cR
    cR
    trcleq2lem
    elabg
    adantr
    mpbird
    cR
    @6
    intss1
    syl
    eqsstrd
    @0
    cR
    @3
    wss
    @1
    cR
    cV
    trclfvlb
    adantr
    eqssd
end
