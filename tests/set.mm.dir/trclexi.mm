include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "cun.mm"
include "wss.mm"
include "ccom.mm"
include "cv.mm"
include "wa.mm"
include "cab.mm"
include "cint.mm"
include "cvv.mm"
include "wcel.mm"
include "ssun1.mm"
include "coundir.mm"
include "coundi.mm"
include "cossxp.mm"
include "dmxpss.mm"
include "xpss1.mm"
include "ax-mp.mm"
include "sstri.mm"
include "unssi.mm"
include "eqsstri.mm"
include "rnxpss.mm"
include "xpss2.mm"
include "xptrrel.mm"
include "ssun2.mm"
include "wex.mm"
include "elexi.mm"
include "dmex.mm"
include "rnex.mm"
include "xpex.mm"
include "unex.mm"
include "trcleq2lem.mm"
include "spcev.mm"
include "intexab.mm"
include "sylib.mm"
include "mp2an.mm"

theorem trclexi
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume trclexi.1: |- A e. V

  disjoint A x
  assert |- |^| { x | ( A C_ x /\ ( x o. x ) C_ x ) } e. _V

  proof
    cA
    cA
    cA
    cdm
    #
    cA
    crn
    #
    cxp
    #
    cun
    #
    wss
    #
    @3
    @3
    ccom
    #
    @3
    wss
    #
    cA
    vx
    cv
    #
    wss
    @7
    @7
    ccom
    @7
    wss
    wa
    #
    vx
    cab
    cint
    cvv
    wcel
    #
    cA
    @2
    ssun1
    @5
    @2
    @3
    @5
    cA
    @3
    ccom
    #
    @2
    @3
    ccom
    #
    cun
    @2
    cA
    @2
    @3
    coundir
    @10
    @11
    @2
    @10
    cA
    cA
    ccom
    #
    cA
    @2
    ccom
    #
    cun
    @2
    cA
    cA
    @2
    coundi
    @12
    @13
    @2
    cA
    cA
    cossxp
    @13
    @2
    cdm
    #
    @1
    cxp
    #
    @2
    cA
    @2
    cossxp
    @14
    @0
    wss
    @15
    @2
    wss
    @0
    @1
    dmxpss
    @14
    @0
    @1
    xpss1
    ax-mp
    sstri
    unssi
    eqsstri
    @11
    @2
    cA
    ccom
    #
    @2
    @2
    ccom
    #
    cun
    @2
    @2
    cA
    @2
    coundi
    @16
    @17
    @2
    @16
    @0
    @2
    crn
    #
    cxp
    #
    @2
    @2
    cA
    cossxp
    @18
    @1
    wss
    @19
    @2
    wss
    @0
    @1
    rnxpss
    @18
    @1
    @0
    xpss2
    ax-mp
    sstri
    @0
    @1
    xptrrel
    unssi
    eqsstri
    unssi
    eqsstri
    @2
    cA
    ssun2
    sstri
    @4
    @6
    wa
    #
    @8
    vx
    wex
    @9
    @8
    @20
    vx
    @3
    cA
    @2
    cA
    cV
    trclexi.1
    elexi
    #
    @0
    @1
    cA
    @21
    dmex
    cA
    @21
    rnex
    xpex
    unex
    @7
    @3
    cA
    trcleq2lem
    spcev
    @8
    vx
    intexab
    sylib
    mp2an
end
