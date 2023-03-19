include "cgru.mm"
include "wcel.mm"
include "cr1.mm"
include "cfv.mm"
include "wss.mm"
include "c0.mm"
include "wceq.mm"
include "wi.mm"
include "con0.mm"
include "cin.mm"
include "inss1.mm"
include "eqsstri.mm"
include "sseq2.mm"
include "mpbii.mm"
include "ss0.mm"
include "fveq2.mm"
include "r10.mm"
include "syl6eq.mm"
include "0ss.mm"
include "syl6eqss.mm"
include "3syl.mm"
include "a1i.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "ciun.mm"
include "cina.mm"
include "cwina.mm"
include "gruina.mm"
include "inawina.mm"
include "wlim.mm"
include "winaon.mm"
include "winalim.mm"
include "r1lim.mm"
include "syl2anc.mm"
include "wral.mm"
include "inss2.mm"
include "sseli.mm"
include "csuc.mm"
include "eleq1.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "simpr.mm"
include "elelsuc.mm"
include "word.mm"
include "wb.mm"
include "ne0i.mm"
include "syl.mm"
include "sylan2.mm"
include "eloni.mm"
include "ordsucelsuc.mm"
include "syl5ibr.mm"
include "mpd.mm"
include "cpw.mm"
include "grupw.mm"
include "ex.mm"
include "adantr.mm"
include "r1suc.mm"
include "biimprcd.mm"
include "syl6.mm"
include "embantd.mm"
include "com23.mm"
include "com4r.mm"
include "ontr1.mm"
include "pm2.27.mm"
include "expd.mm"
include "com3r.mm"
include "sylc.mm"
include "imp.mm"
include "ralimdva.mm"
include "gruiun.mm"
include "3expia.mm"
include "syld.mm"
include "cvv.mm"
include "vex.mm"
include "mpan.mm"
include "biimprd.mm"
include "sylan9r.mm"
include "exp32.mm"
include "com34.mm"
include "tfinds2.mm"
include "impcom.mm"
include "gruelss.mm"
include "syldan.mm"
include "ralrimiva.mm"
include "iunss.mm"
include "sylibr.mm"
include "eqsstrd.mm"
include "pm2.61dne.mm"

theorem grur1a
  let cA: class A
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  assume gruina.1: |- A = ( U i^i On )


  assert |- ( U e. Univ -> ( R1 ` A ) C_ U )

  proof
    cU
    cgru
    wcel
    #
    cA
    cr1
    cfv
    #
    cU
    wss
    #
    cU
    c0
    cU
    c0
    wceq
    #
    @2
    wi
    @0
    @3
    cA
    c0
    wss
    #
    cA
    c0
    wceq
    #
    @2
    @3
    cA
    cU
    wss
    @4
    cA
    cU
    con0
    cin
    #
    cU
    gruina.1
    cU
    con0
    inss1
    eqsstri
    #
    cU
    c0
    cA
    sseq2
    mpbii
    cA
    ss0
    @5
    @1
    c0
    cU
    @5
    @1
    c0
    cr1
    cfv
    #
    c0
    cA
    c0
    cr1
    fveq2
    r10
    syl6eq
    cU
    0ss
    syl6eqss
    3syl
    a1i
    @0
    cU
    c0
    wne
    #
    @2
    @0
    @9
    wa
    #
    @1
    vx
    cA
    vx
    cv
    #
    cr1
    cfv
    #
    ciun
    #
    cU
    @10
    cA
    cina
    wcel
    #
    cA
    cwina
    wcel
    #
    @1
    @13
    wceq
    #
    cA
    cU
    gruina.1
    gruina
    #
    cA
    inawina
    #
    @15
    cA
    con0
    wcel
    #
    cA
    wlim
    @16
    cA
    winaon
    #
    cA
    winalim
    vx
    cA
    con0
    r1lim
    syl2anc
    3syl
    @0
    @13
    cU
    wss
    #
    @9
    @0
    @12
    cU
    wss
    #
    vx
    cA
    wral
    @21
    @0
    @22
    vx
    cA
    @0
    @11
    cA
    wcel
    #
    @12
    cU
    wcel
    #
    @22
    @23
    @0
    @24
    @23
    @11
    con0
    wcel
    #
    @0
    @24
    wi
    cA
    con0
    @11
    cA
    @6
    con0
    gruina.1
    cU
    con0
    inss2
    eqsstri
    sseli
    @25
    @0
    @23
    @24
    @23
    @24
    wi
    c0
    cA
    wcel
    #
    c0
    cU
    wcel
    #
    wi
    #
    vy
    cv
    #
    cA
    wcel
    #
    @29
    cr1
    cfv
    #
    cU
    wcel
    #
    wi
    #
    @29
    csuc
    #
    cA
    wcel
    #
    @34
    cr1
    cfv
    #
    cU
    wcel
    #
    wi
    @0
    vx
    vy
    @11
    c0
    wceq
    #
    @23
    @26
    @24
    @27
    @11
    c0
    cA
    eleq1
    @38
    @12
    c0
    cU
    @38
    @12
    @8
    c0
    @11
    c0
    cr1
    fveq2
    r10
    syl6eq
    eleq1d
    imbi12d
    @11
    @29
    wceq
    #
    @23
    @30
    @24
    @32
    @11
    @29
    cA
    eleq1
    @39
    @12
    @31
    cU
    @11
    @29
    cr1
    fveq2
    eleq1d
    imbi12d
    @11
    @34
    wceq
    #
    @23
    @35
    @24
    @37
    @11
    @34
    cA
    eleq1
    @40
    @12
    @36
    cU
    @11
    @34
    cr1
    fveq2
    eleq1d
    imbi12d
    @28
    @0
    cA
    cU
    c0
    @7
    sseli
    a1i
    @0
    @33
    @35
    @29
    con0
    wcel
    #
    @37
    @0
    @35
    @33
    @41
    @37
    wi
    #
    @0
    @35
    @33
    @42
    wi
    @0
    @35
    wa
    #
    @30
    @32
    @42
    @43
    @35
    @30
    @0
    @35
    simpr
    @35
    @30
    @43
    @34
    cA
    csuc
    wcel
    #
    @34
    cA
    elelsuc
    @43
    @19
    cA
    word
    @30
    @44
    wb
    @35
    @0
    @9
    @19
    @35
    @34
    cU
    wcel
    @9
    cA
    cU
    @34
    @7
    sseli
    cU
    @34
    ne0i
    syl
    @10
    @14
    @15
    @19
    @17
    @18
    @20
    3syl
    #
    sylan2
    cA
    eloni
    @29
    cA
    ordsucelsuc
    3syl
    syl5ibr
    mpd
    @43
    @32
    @31
    cpw
    #
    cU
    wcel
    #
    @42
    @0
    @32
    @47
    wi
    @35
    @0
    @32
    @47
    @31
    cU
    grupw
    ex
    adantr
    @41
    @37
    @47
    @41
    @36
    @46
    cU
    @29
    r1suc
    eleq1d
    biimprcd
    syl6
    embantd
    ex
    com23
    com4r
    @11
    wlim
    #
    @0
    @23
    @33
    vy
    @11
    wral
    #
    @24
    @48
    @0
    @23
    @49
    @24
    wi
    @0
    @23
    wa
    #
    @49
    vy
    @11
    @31
    ciun
    #
    cU
    wcel
    #
    @48
    @24
    @50
    @49
    @32
    vy
    @11
    wral
    #
    @52
    @50
    @33
    @32
    vy
    @11
    @50
    @29
    @11
    wcel
    #
    @33
    @32
    wi
    #
    @50
    @23
    @19
    @54
    @55
    wi
    @0
    @23
    simpr
    @23
    @0
    @9
    @19
    @23
    @11
    cU
    wcel
    #
    @9
    cA
    cU
    @11
    @7
    sseli
    #
    cU
    @11
    ne0i
    syl
    @45
    sylan2
    @19
    @54
    @23
    @55
    @19
    @54
    @23
    @55
    @19
    @54
    @23
    wa
    @30
    @55
    @29
    @11
    cA
    ontr1
    @30
    @32
    pm2.27
    syl6
    expd
    com3r
    sylc
    imp
    ralimdva
    @23
    @0
    @56
    @53
    @52
    wi
    @57
    @0
    @56
    @53
    @52
    vy
    @11
    @31
    cU
    gruiun
    3expia
    sylan2
    syld
    @48
    @24
    @52
    @48
    @12
    @51
    cU
    @11
    cvv
    wcel
    @48
    @12
    @51
    wceq
    vx
    vex
    vy
    @11
    cvv
    r1lim
    mpan
    eleq1d
    biimprd
    sylan9r
    exp32
    com34
    tfinds2
    com3r
    mpd
    impcom
    @12
    cU
    gruelss
    syldan
    ralrimiva
    vx
    cA
    @12
    cU
    iunss
    sylibr
    adantr
    eqsstrd
    ex
    pm2.61dne
end
