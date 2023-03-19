include "cxp.mm"
include "cin.mm"
include "crn.mm"
include "wceq.mm"
include "wss.mm"
include "cres.mm"
include "inss2.mm"
include "rnss.mm"
include "ax-mp.mm"
include "rnxpss.mm"
include "sstri.mm"
include "eqss.mm"
include "mpbiran.mm"
include "cvv.mm"
include "ssid.mm"
include "ssv.mm"
include "xpss12.mm"
include "mp2an.mm"
include "sslin.mm"
include "df-res.mm"
include "sseqtr4i.mm"
include "sstr.mm"
include "mpan2.mm"
include "cv.mm"
include "wcel.mm"
include "cop.mm"
include "wex.mm"
include "wa.mm"
include "ssel.mm"
include "vex.mm"
include "elrn2.mm"
include "syl6ib.mm"
include "ancrd.mm"
include "elin.mm"
include "opelxp.mm"
include "anbi2i.mm"
include "opelres.mm"
include "anbi1i.mm"
include "anass.mm"
include "bitr2i.mm"
include "3bitri.mm"
include "exbii.mm"
include "19.41v.mm"
include "syl6ibr.mm"
include "ssrdv.mm"
include "impbii.mm"

theorem ssrnres
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y


  assert |- ( B C_ ran ( C |` A ) <-> ran ( C i^i ( A X. B ) ) = B )

  proof
    cC
    cA
    cB
    cxp
    #
    cin
    #
    crn
    #
    cB
    wceq
    #
    cB
    @2
    wss
    #
    cB
    cC
    cA
    cres
    #
    crn
    #
    wss
    #
    @3
    @2
    cB
    wss
    @4
    @2
    @0
    crn
    #
    cB
    @1
    @0
    wss
    @2
    @8
    wss
    cC
    @0
    inss2
    @1
    @0
    rnss
    ax-mp
    cA
    cB
    rnxpss
    sstri
    @2
    cB
    eqss
    mpbiran
    @4
    @7
    @4
    @2
    @6
    wss
    #
    @7
    @1
    @5
    wss
    @9
    @1
    cC
    cA
    cvv
    cxp
    #
    cin
    #
    @5
    @0
    @10
    wss
    #
    @1
    @11
    wss
    cA
    cA
    wss
    cB
    cvv
    wss
    @12
    cA
    ssid
    cB
    ssv
    cA
    cA
    cB
    cvv
    xpss12
    mp2an
    @0
    @10
    cC
    sslin
    ax-mp
    cC
    cA
    df-res
    sseqtr4i
    @1
    @5
    rnss
    ax-mp
    cB
    @2
    @6
    sstr
    mpan2
    @7
    vy
    cB
    @2
    @7
    vy
    cv
    #
    cB
    wcel
    #
    vx
    cv
    #
    @13
    cop
    #
    @5
    wcel
    #
    vx
    wex
    #
    @14
    wa
    #
    @13
    @2
    wcel
    #
    @7
    @14
    @18
    @7
    @14
    @13
    @6
    wcel
    @18
    cB
    @6
    @13
    ssel
    vx
    @13
    @5
    vy
    vex
    #
    elrn2
    syl6ib
    ancrd
    @20
    @16
    @1
    wcel
    #
    vx
    wex
    @17
    @14
    wa
    #
    vx
    wex
    @19
    vx
    @13
    @1
    @21
    elrn2
    @22
    @23
    vx
    @22
    @16
    cC
    wcel
    #
    @16
    @0
    wcel
    #
    wa
    @24
    @15
    cA
    wcel
    #
    @14
    wa
    #
    wa
    #
    @23
    @16
    cC
    @0
    elin
    @25
    @27
    @24
    @15
    @13
    cA
    cB
    opelxp
    anbi2i
    @23
    @24
    @26
    wa
    #
    @14
    wa
    @28
    @17
    @29
    @14
    @15
    @13
    cC
    cA
    @21
    opelres
    anbi1i
    @24
    @26
    @14
    anass
    bitr2i
    3bitri
    exbii
    @17
    @14
    vx
    19.41v
    3bitri
    syl6ibr
    ssrdv
    impbii
    bitr2i
end
