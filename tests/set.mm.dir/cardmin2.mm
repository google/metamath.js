include "cv.mm"
include "csdm.mm"
include "wbr.mm"
include "con0.mm"
include "wrex.mm"
include "crab.mm"
include "cint.mm"
include "ccrd.mm"
include "cfv.mm"
include "wceq.mm"
include "wcel.mm"
include "wral.mm"
include "onintrab2.mm"
include "biimpi.mm"
include "wa.mm"
include "cdom.mm"
include "cen.mm"
include "wn.mm"
include "wss.mm"
include "adantr.mm"
include "word.mm"
include "eloni.mm"
include "ordelss.mm"
include "sylan.mm"
include "sylanb.mm"
include "ssdomg.mm"
include "sylc.mm"
include "onelon.mm"
include "wi.mm"
include "nfcv.mm"
include "nfrab1.mm"
include "nfint.mm"
include "nfbr.mm"
include "breq2.mm"
include "onminsb.mm"
include "sdomentr.mm"
include "elrab.mm"
include "ssrab2.mm"
include "onnmin.mm"
include "mpan.mm"
include "sylbir.mm"
include "expcom.mm"
include "syl.mm"
include "impancom.mm"
include "con2d.mm"
include "mpd.mm"
include "ensym.mm"
include "nsyl.mm"
include "brsdom.mm"
include "sylanbrc.mm"
include "ralrimiva.mm"
include "iscard.mm"
include "c0.mm"
include "wne.mm"
include "cvv.mm"
include "vprc.mm"
include "inteq.mm"
include "int0.mm"
include "syl6eq.mm"
include "eleq1d.mm"
include "mtbiri.mm"
include "fvex.mm"
include "eleq1.mm"
include "mpbii.mm"
include "necon2ai.mm"
include "rabn0.mm"
include "sylib.mm"
include "impbii.mm"

theorem cardmin2
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint A y
  disjoint x y
  assert |- ( E. x e. On A ~< x <-> ( card ` |^| { x e. On | A ~< x } ) = |^| { x e. On | A ~< x } )

  proof
    cA
    vx
    cv
    #
    csdm
    wbr
    #
    vx
    con0
    wrex
    #
    @1
    vx
    con0
    crab
    #
    cint
    #
    ccrd
    cfv
    #
    @4
    wceq
    #
    @2
    @4
    con0
    wcel
    #
    vy
    cv
    #
    @4
    csdm
    wbr
    #
    vy
    @4
    wral
    @6
    @2
    @7
    @1
    vx
    onintrab2
    #
    biimpi
    #
    @2
    @9
    vy
    @4
    @2
    @8
    @4
    wcel
    #
    wa
    #
    @8
    @4
    cdom
    wbr
    #
    @8
    @4
    cen
    wbr
    #
    wn
    @9
    @13
    @7
    @8
    @4
    wss
    #
    @14
    @2
    @7
    @12
    @11
    adantr
    @2
    @7
    @12
    @16
    @10
    @7
    @4
    word
    @12
    @16
    @4
    eloni
    @4
    @8
    ordelss
    sylan
    sylanb
    @8
    @4
    con0
    ssdomg
    sylc
    @13
    @4
    @8
    cen
    wbr
    #
    @15
    @13
    @8
    con0
    wcel
    #
    @17
    wn
    #
    @2
    @7
    @12
    @18
    @10
    @4
    @8
    onelon
    sylanb
    @2
    @18
    @12
    @19
    @2
    @18
    wa
    @17
    @12
    @2
    @17
    @18
    @12
    wn
    #
    @2
    @17
    wa
    cA
    @8
    csdm
    wbr
    #
    @18
    @20
    wi
    @2
    cA
    @4
    csdm
    wbr
    #
    @17
    @21
    @1
    @22
    vx
    vx
    cA
    @4
    csdm
    vx
    cA
    nfcv
    vx
    csdm
    nfcv
    vx
    @3
    @1
    vx
    con0
    nfrab1
    nfint
    nfbr
    @0
    @4
    cA
    csdm
    breq2
    onminsb
    cA
    @4
    @8
    sdomentr
    sylan
    @18
    @21
    @20
    @18
    @21
    wa
    @8
    @3
    wcel
    #
    @20
    @1
    @21
    vx
    @8
    con0
    @0
    @8
    cA
    csdm
    breq2
    elrab
    @3
    con0
    wss
    @23
    @20
    @1
    vx
    con0
    ssrab2
    @3
    @8
    onnmin
    mpan
    sylbir
    expcom
    syl
    impancom
    con2d
    impancom
    mpd
    @8
    @4
    ensym
    nsyl
    @8
    @4
    brsdom
    sylanbrc
    ralrimiva
    vy
    @4
    iscard
    sylanbrc
    @6
    @3
    c0
    wne
    @2
    @6
    @3
    c0
    @3
    c0
    wceq
    #
    @4
    cvv
    wcel
    #
    @6
    @24
    @25
    cvv
    cvv
    wcel
    vprc
    @24
    @4
    cvv
    cvv
    @24
    @4
    c0
    cint
    cvv
    @3
    c0
    inteq
    int0
    syl6eq
    eleq1d
    mtbiri
    @6
    @5
    cvv
    wcel
    @25
    @4
    ccrd
    fvex
    @5
    @4
    cvv
    eleq1
    mpbii
    nsyl
    necon2ai
    @1
    vx
    con0
    rabn0
    sylib
    impbii
end
