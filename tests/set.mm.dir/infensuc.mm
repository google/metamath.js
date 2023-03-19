include "con0.mm"
include "wcel.mm"
include "com.mm"
include "wss.mm"
include "wa.mm"
include "csuc.mm"
include "cen.mm"
include "wbr.mm"
include "wceq.mm"
include "cvv.mm"
include "onprc.mm"
include "eleq1.mm"
include "mtbiri.mm"
include "ssexg.mm"
include "ancoms.mm"
include "nsyl3.mm"
include "omon.mm"
include "ori.mm"
include "nsyl2.mm"
include "wi.mm"
include "cv.mm"
include "id.mm"
include "suceq.mm"
include "breq12d.mm"
include "weq.mm"
include "limom.mm"
include "limensuci.mm"
include "csn.mm"
include "vex.mm"
include "sucex.mm"
include "en2sn.mm"
include "mp2an.mm"
include "cin.mm"
include "c0.mm"
include "wel.mm"
include "wn.mm"
include "word.mm"
include "eloni.mm"
include "ordirr.mm"
include "syl.mm"
include "disjsn.mm"
include "sylibr.mm"
include "sucelon.mm"
include "3imtr4i.mm"
include "jca.mm"
include "cun.mm"
include "unen.mm"
include "df-suc.mm"
include "3brtr4g.mm"
include "ex.mm"
include "syl5.mm"
include "mpan2.mm"
include "com12.mm"
include "ad2antrr.mm"
include "wlim.mm"
include "wral.mm"
include "limensuc.mm"
include "mpan.mm"
include "a1d.mm"
include "tfindsg.mm"
include "exp31.mm"
include "com23.mm"
include "imp.mm"
include "mpd.mm"

theorem infensuc
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. On /\ _om C_ A ) -> A ~~ suc A )

  proof
    cA
    con0
    wcel
    #
    com
    cA
    wss
    #
    wa
    #
    com
    con0
    wcel
    #
    cA
    cA
    csuc
    #
    cen
    wbr
    #
    @2
    com
    con0
    wceq
    #
    @3
    @6
    com
    cvv
    wcel
    #
    @2
    @6
    @7
    con0
    cvv
    wcel
    onprc
    com
    con0
    cvv
    eleq1
    mtbiri
    @1
    @0
    @7
    com
    cA
    con0
    ssexg
    ancoms
    nsyl3
    @3
    @6
    omon
    ori
    nsyl2
    @0
    @1
    @3
    @5
    wi
    @0
    @3
    @1
    @5
    @0
    @3
    @1
    @5
    vx
    cv
    #
    @8
    csuc
    #
    cen
    wbr
    #
    com
    com
    csuc
    #
    cen
    wbr
    vy
    cv
    #
    @12
    csuc
    #
    cen
    wbr
    #
    @13
    @13
    csuc
    #
    cen
    wbr
    #
    @5
    vx
    vy
    cA
    com
    @8
    com
    wceq
    #
    @8
    com
    @9
    @11
    cen
    @17
    id
    @8
    com
    suceq
    breq12d
    vx
    vy
    weq
    #
    @8
    @12
    @9
    @13
    cen
    @18
    id
    @8
    @12
    suceq
    breq12d
    @8
    @13
    wceq
    #
    @8
    @13
    @9
    @15
    cen
    @19
    id
    @8
    @13
    suceq
    breq12d
    @8
    cA
    wceq
    #
    @8
    cA
    @9
    @4
    cen
    @20
    id
    @8
    cA
    suceq
    breq12d
    com
    con0
    limom
    limensuci
    @12
    con0
    wcel
    #
    @14
    @16
    wi
    @3
    com
    @12
    wss
    #
    @14
    @21
    @16
    @14
    @12
    csn
    #
    @13
    csn
    #
    cen
    wbr
    #
    @21
    @16
    wi
    @12
    cvv
    wcel
    @13
    cvv
    wcel
    @25
    vy
    vex
    #
    @12
    @26
    sucex
    @12
    @13
    cvv
    cvv
    en2sn
    mp2an
    @21
    @12
    @23
    cin
    c0
    wceq
    #
    @13
    @24
    cin
    c0
    wceq
    #
    wa
    #
    @14
    @25
    wa
    #
    @16
    @21
    @27
    @28
    @21
    vy
    vy
    wel
    wn
    #
    @27
    @21
    @12
    word
    @31
    @12
    eloni
    @12
    ordirr
    syl
    @12
    @12
    disjsn
    sylibr
    @13
    con0
    wcel
    #
    @13
    @13
    wcel
    wn
    #
    @21
    @28
    @32
    @13
    word
    @33
    @13
    eloni
    @13
    ordirr
    syl
    @12
    sucelon
    @13
    @13
    disjsn
    3imtr4i
    jca
    @30
    @29
    @16
    @30
    @29
    wa
    @12
    @23
    cun
    @13
    @24
    cun
    @13
    @15
    cen
    @12
    @13
    @23
    @24
    unen
    @12
    df-suc
    @13
    df-suc
    3brtr4g
    ex
    syl5
    mpan2
    com12
    ad2antrr
    @8
    wlim
    #
    @3
    wa
    com
    @8
    wss
    #
    wa
    @10
    @22
    @14
    wi
    vy
    @8
    wral
    @34
    @10
    @3
    @35
    @8
    cvv
    wcel
    @34
    @10
    vx
    vex
    @8
    cvv
    limensuc
    mpan
    ad2antrr
    a1d
    tfindsg
    exp31
    com23
    imp
    mpd
end
