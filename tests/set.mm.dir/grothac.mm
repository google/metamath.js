include "ccrd.mm"
include "cdm.mm"
include "cvv.mm"
include "cv.mm"
include "wcel.mm"
include "cpw.mm"
include "wss.mm"
include "wa.mm"
include "wral.mm"
include "csdm.mm"
include "wbr.mm"
include "wi.mm"
include "w3a.mm"
include "crab.mm"
include "weq.mm"
include "pweq.mm"
include "sseq1d.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "rspcva.mm"
include "simpld.mm"
include "rabss.mm"
include "biimpri.mm"
include "cdom.mm"
include "vex.mm"
include "canth2.mm"
include "sdomdom.mm"
include "ax-mp.mm"
include "ssdomg.mm"
include "domtr.mm"
include "sylancr.mm"
include "tskwe.mm"
include "mpan.mm"
include "numdom.mm"
include "expcom.mm"
include "syl2im.mm"
include "3impia.mm"
include "axgroth6.mm"
include "exlimiiv.mm"
include "2th.mm"
include "eqriv.mm"

theorem grothac
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u


  assert |- dom card = _V

  proof
    vy
    ccrd
    cdm
    #
    cvv
    vy
    cv
    #
    @0
    wcel
    #
    @1
    cvv
    wcel
    @1
    vu
    cv
    #
    wcel
    #
    vx
    cv
    #
    cpw
    #
    @3
    wss
    #
    @6
    @3
    wcel
    #
    wa
    #
    vx
    @3
    wral
    #
    @5
    @3
    csdm
    wbr
    #
    @5
    @3
    wcel
    wi
    vx
    @3
    cpw
    #
    wral
    #
    w3a
    @2
    vu
    @4
    @10
    @13
    @2
    @4
    @10
    wa
    #
    @1
    cpw
    #
    @3
    wss
    #
    @13
    @11
    vx
    @12
    crab
    @3
    wss
    #
    @2
    @14
    @16
    @15
    @3
    wcel
    #
    @9
    @16
    @18
    wa
    vx
    @1
    @3
    vx
    vy
    weq
    #
    @7
    @16
    @8
    @18
    @19
    @6
    @15
    @3
    @5
    @1
    pweq
    #
    sseq1d
    @19
    @6
    @15
    @3
    @20
    eleq1d
    anbi12d
    rspcva
    simpld
    @17
    @13
    @11
    vx
    @12
    @3
    rabss
    biimpri
    @16
    @1
    @3
    cdom
    wbr
    #
    @17
    @3
    @0
    wcel
    #
    @2
    @16
    @1
    @15
    cdom
    wbr
    #
    @15
    @3
    cdom
    wbr
    #
    @21
    @1
    @15
    csdm
    wbr
    @23
    @1
    vy
    vex
    #
    canth2
    @1
    @15
    sdomdom
    ax-mp
    @3
    cvv
    wcel
    #
    @16
    @24
    wi
    vu
    vex
    #
    @15
    @3
    cvv
    ssdomg
    ax-mp
    @1
    @15
    @3
    domtr
    sylancr
    @26
    @17
    @22
    @27
    vx
    @3
    cvv
    tskwe
    mpan
    @22
    @21
    @2
    @3
    @1
    numdom
    expcom
    syl2im
    syl2im
    3impia
    vy
    vu
    vx
    axgroth6
    exlimiiv
    @25
    2th
    eqriv
end
