include "crpss.mm"
include "wor.mm"
include "cv.mm"
include "wss.mm"
include "wo.mm"
include "cdif.mm"
include "wcel.mm"
include "cpw.mm"
include "crab.mm"
include "wral.mm"
include "wa.mm"
include "weq.mm"
include "difeq2.mm"
include "eleq1d.mm"
include "elrab.mm"
include "an4.mm"
include "biimpi.mm"
include "syl2anb.mm"
include "wi.mm"
include "sorpssi.mm"
include "expcom.mm"
include "wceq.mm"
include "selpw.mm"
include "dfss4.mm"
include "bitri.mm"
include "sscon.mm"
include "sseq12.mm"
include "syl5ib.mm"
include "wb.mm"
include "ancoms.mm"
include "orim12d.mm"
include "com12.mm"
include "orcoms.mm"
include "syl6.mm"
include "com3l.mm"
include "impd.mm"
include "syl5.mm"
include "ralrimivv.mm"
include "sorpss.mm"
include "sylibr.mm"

theorem sorpsscmpl
  let vu: setvar u
  let cA: class A
  let cY: class Y
  let vx: setvar x
  let vy: setvar y

  disjoint Y u
  disjoint A u
  disjoint Y x
  disjoint Y y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint u x
  disjoint u y
  assert |- ( [C.] Or Y -> [C.] Or { u e. ~P A | ( A \ u ) e. Y } )

  proof
    cY
    crpss
    wor
    #
    vx
    cv
    #
    vy
    cv
    #
    wss
    #
    @2
    @1
    wss
    #
    wo
    #
    vy
    cA
    vu
    cv
    #
    cdif
    #
    cY
    wcel
    #
    vu
    cA
    cpw
    #
    crab
    #
    wral
    vx
    @10
    wral
    @10
    crpss
    wor
    @0
    @5
    vx
    vy
    @10
    @10
    @1
    @10
    wcel
    #
    @2
    @10
    wcel
    #
    wa
    @1
    @9
    wcel
    #
    @2
    @9
    wcel
    #
    wa
    #
    cA
    @1
    cdif
    #
    cY
    wcel
    #
    cA
    @2
    cdif
    #
    cY
    wcel
    #
    wa
    #
    wa
    #
    @0
    @5
    @11
    @13
    @17
    wa
    #
    @14
    @19
    wa
    #
    @21
    @12
    @8
    @17
    vu
    @1
    @9
    vu
    vx
    weq
    @7
    @16
    cY
    @6
    @1
    cA
    difeq2
    eleq1d
    elrab
    @8
    @19
    vu
    @2
    @9
    vu
    vy
    weq
    @7
    @18
    cY
    @6
    @2
    cA
    difeq2
    eleq1d
    elrab
    @22
    @23
    wa
    @21
    @13
    @17
    @14
    @19
    an4
    biimpi
    syl2anb
    @0
    @15
    @20
    @5
    @20
    @0
    @15
    @5
    @20
    @0
    @16
    @18
    wss
    #
    @18
    @16
    wss
    #
    wo
    #
    @15
    @5
    wi
    #
    @0
    @20
    @26
    cY
    @16
    @18
    sorpssi
    expcom
    @25
    @24
    @27
    @15
    @25
    @24
    wo
    #
    @5
    @13
    cA
    @16
    cdif
    #
    @1
    wceq
    #
    cA
    @18
    cdif
    #
    @2
    wceq
    #
    @28
    @5
    wi
    @14
    @13
    @1
    cA
    wss
    @30
    vx
    cA
    selpw
    @1
    cA
    dfss4
    bitri
    @14
    @2
    cA
    wss
    @32
    vy
    cA
    selpw
    @2
    cA
    dfss4
    bitri
    @30
    @32
    wa
    #
    @25
    @3
    @24
    @4
    @25
    @29
    @31
    wss
    @33
    @3
    @18
    @16
    cA
    sscon
    @29
    @1
    @31
    @2
    sseq12
    syl5ib
    @24
    @31
    @29
    wss
    #
    @33
    @4
    @16
    @18
    cA
    sscon
    @32
    @30
    @34
    @4
    wb
    @31
    @2
    @29
    @1
    sseq12
    ancoms
    syl5ib
    orim12d
    syl2anb
    com12
    orcoms
    syl6
    com3l
    impd
    syl5
    ralrimivv
    vx
    vy
    @10
    sorpss
    sylibr
end
