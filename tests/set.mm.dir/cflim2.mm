include "wlim.mm"
include "ccf.mm"
include "cfv.mm"
include "com.mm"
include "wss.mm"
include "cv.mm"
include "cuni.mm"
include "wceq.mm"
include "cpw.mm"
include "crab.mm"
include "ccrd.mm"
include "ciin.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "rabid.mm"
include "selpw.mm"
include "w3a.mm"
include "wn.mm"
include "cep.mm"
include "ccnv.mm"
include "wbr.mm"
include "wrex.mm"
include "wel.mm"
include "con0.mm"
include "word.mm"
include "wi.mm"
include "limord.mm"
include "ordsson.mm"
include "sstr.mm"
include "expcom.mm"
include "3syl.mm"
include "imp.mm"
include "3adant3.mm"
include "ssel2.mm"
include "eloni.mm"
include "ordirr.mm"
include "ssel.mm"
include "com12.mm"
include "adantl.mm"
include "mtod.mm"
include "sylan.mm"
include "simpl2.mm"
include "mtand.mm"
include "simpl3.mm"
include "sseq1d.mm"
include "mtbird.mm"
include "unissb.mm"
include "sylnib.mm"
include "nrexdv.mm"
include "wb.mm"
include "ontri1.mm"
include "ancoms.mm"
include "vex.mm"
include "brcnv.mm"
include "epel.mm"
include "bitri.mm"
include "notbii.mm"
include "syl6bbr.mm"
include "a1i.mm"
include "syl2and.mm"
include "impl.mm"
include "ralbidva.mm"
include "rexbidva.mm"
include "syl.mm"
include "mtbid.mm"
include "cvv.mm"
include "wfr.mm"
include "c0.mm"
include "wne.mm"
include "wwe.mm"
include "wor.mm"
include "cfn.mm"
include "epweon.mm"
include "wess.mm"
include "mpi.mm"
include "weso.mm"
include "cnvso.mm"
include "sylib.mm"
include "adantr.mm"
include "csdm.mm"
include "cen.mm"
include "cdm.mm"
include "onssnum.mm"
include "mpan.mm"
include "cardid2.mm"
include "ensym.mm"
include "nnsdom.mm"
include "ensdomtr.mm"
include "syl2an.mm"
include "isfinite.mm"
include "sylibr.mm"
include "wofi.mm"
include "syl2anc.mm"
include "wefr.mm"
include "ssid.mm"
include "unieq.mm"
include "uni0.mm"
include "syl6eq.mm"
include "eqeq1.mm"
include "syl5ib.mm"
include "nlim0.mm"
include "limeq.mm"
include "mtbiri.mm"
include "syl6.mm"
include "necon2ad.mm"
include "impcom.mm"
include "3adant2.mm"
include "fri.mm"
include "syl22anc.mm"
include "cardon.mm"
include "ordom.mm"
include "ordtri1.mm"
include "mp2b.mm"
include "syl3an2b.mm"
include "3expb.mm"
include "sylan2b.mm"
include "ralrimiva.mm"
include "ssiin.mm"
include "cflim3.mm"
include "sseqtr4d.mm"
include "cab.mm"
include "cint.mm"
include "fvex.mm"
include "dfiin2.mm"
include "cardlim.mm"
include "sseq2.mm"
include "bibi12d.mm"
include "mpbiri.mm"
include "rexlimivw.mm"
include "ss2abi.mm"
include "eleq1.mm"
include "abssi.mm"
include "syl6eqelr.mm"
include "intex.mm"
include "onint.mm"
include "sylancr.mm"
include "sseldi.mm"
include "eqeltrd.mm"
include "elab.mm"
include "mpbid.mm"
include "csuc.mm"
include "wo.mm"
include "w3o.mm"
include "ordzsl.mm"
include "df-3or.mm"
include "orcom.mm"
include "df-or.mm"
include "3bitri.mm"
include "fveq2.mm"
include "cf0.mm"
include "c1o.mm"
include "1n0.mm"
include "csn.mm"
include "df1o2.mm"
include "unieqi.mm"
include "0ex.mm"
include "unisn.mm"
include "eqtri.mm"
include "neeqtrri.mm"
include "limuni.mm"
include "necon3ai.mm"
include "ax-mp.mm"
include "cfsuc.mm"
include "sylan9eqr.mm"
include "rexlimiva.mm"
include "jaoi.mm"
include "con4d.mm"
include "cff.mm"
include "fdmi.mm"
include "eleq2i.mm"
include "ndmfv.mm"
include "sylnbir.mm"
include "pm2.21d.mm"
include "pm2.61i.mm"
include "impbii.mm"

theorem cflim2
  let cA: class A
  let vs: setvar s
  let vy: setvar y
  let vx: setvar x
  let vt: setvar t
  assume cflim2.1: |- A e. _V


  assert |- ( Lim A <-> Lim ( cf ` A ) )

  proof
    cA
    wlim
    #
    cA
    ccf
    cfv
    #
    wlim
    #
    @0
    com
    @1
    wss
    #
    @2
    @0
    com
    vy
    vy
    cv
    #
    cuni
    #
    cA
    wceq
    #
    vy
    cA
    cpw
    #
    crab
    #
    @4
    ccrd
    cfv
    #
    ciin
    #
    @1
    @0
    com
    @9
    wss
    #
    vy
    @8
    wral
    com
    @10
    wss
    @0
    @11
    vy
    @8
    @4
    @8
    wcel
    @0
    @4
    @7
    wcel
    #
    @6
    wa
    @11
    @6
    vy
    @7
    rabid
    @0
    @12
    @6
    @11
    @12
    @0
    @4
    cA
    wss
    #
    @6
    @11
    vy
    cA
    selpw
    @0
    @13
    @6
    w3a
    #
    @9
    com
    wcel
    #
    wn
    #
    @11
    @14
    @15
    vt
    cv
    #
    vs
    cv
    #
    cep
    ccnv
    #
    wbr
    #
    wn
    #
    vt
    @4
    wral
    #
    vs
    @4
    wrex
    #
    @14
    @17
    @18
    wss
    #
    vt
    @4
    wral
    #
    vs
    @4
    wrex
    #
    @23
    @14
    @25
    vs
    @4
    @14
    vs
    vy
    wel
    #
    wa
    #
    @5
    @18
    wss
    #
    @25
    @28
    @29
    cA
    @18
    wss
    #
    @28
    @30
    @4
    @18
    wss
    #
    @14
    @4
    con0
    wss
    #
    @27
    @31
    wn
    @0
    @13
    @32
    @6
    @0
    @13
    @32
    @0
    cA
    word
    #
    cA
    con0
    wss
    #
    @13
    @32
    wi
    cA
    limord
    cA
    ordsson
    @13
    @34
    @32
    @4
    cA
    con0
    sstr
    expcom
    3syl
    imp
    3adant3
    #
    @32
    @27
    wa
    #
    @31
    vs
    vs
    wel
    #
    @36
    @18
    con0
    wcel
    #
    @18
    word
    @37
    wn
    @4
    con0
    @18
    ssel2
    @18
    eloni
    @18
    ordirr
    3syl
    @27
    @31
    @37
    wi
    @32
    @31
    @27
    @37
    @4
    @18
    @18
    ssel
    com12
    adantl
    mtod
    sylan
    @28
    @13
    @30
    @31
    @0
    @13
    @6
    @27
    simpl2
    @4
    cA
    @18
    sstr
    sylan
    mtand
    @28
    @5
    cA
    @18
    @0
    @13
    @6
    @27
    simpl3
    sseq1d
    mtbird
    vt
    @4
    @18
    unissb
    sylnib
    nrexdv
    @14
    @32
    @26
    @23
    wb
    @35
    @32
    @25
    @22
    vs
    @4
    @36
    @24
    @21
    vt
    @4
    @32
    @27
    vt
    vy
    wel
    #
    @24
    @21
    wb
    #
    @32
    @27
    @38
    @39
    @17
    con0
    wcel
    #
    @40
    @4
    con0
    @18
    ssel
    @4
    con0
    @17
    ssel
    @38
    @41
    wa
    #
    @40
    wi
    @32
    @42
    @24
    vs
    vt
    wel
    #
    wn
    #
    @21
    @41
    @38
    @24
    @44
    wb
    @17
    @18
    ontri1
    ancoms
    @20
    @43
    @20
    @18
    @17
    cep
    wbr
    @43
    @17
    @18
    cep
    vt
    vex
    vs
    vex
    brcnv
    vs
    vt
    epel
    bitri
    notbii
    syl6bbr
    a1i
    syl2and
    impl
    ralbidva
    rexbidva
    syl
    mtbid
    @14
    @15
    wa
    #
    @4
    cvv
    wcel
    #
    @4
    @19
    wfr
    #
    @4
    @4
    wss
    #
    @4
    c0
    wne
    #
    @23
    @46
    @45
    vy
    vex
    #
    a1i
    @45
    @4
    @19
    wwe
    #
    @47
    @14
    @32
    @15
    @51
    @35
    @32
    @15
    wa
    #
    @4
    @19
    wor
    #
    @4
    cfn
    wcel
    #
    @51
    @32
    @53
    @15
    @32
    @4
    cep
    wor
    #
    @53
    @32
    @4
    cep
    wwe
    #
    @55
    @32
    con0
    cep
    wwe
    @56
    epweon
    @4
    con0
    cep
    wess
    mpi
    @4
    cep
    weso
    syl
    @4
    cep
    cnvso
    sylib
    adantr
    @52
    @4
    com
    csdm
    wbr
    #
    @54
    @32
    @4
    @9
    cen
    wbr
    #
    @9
    com
    csdm
    wbr
    @57
    @15
    @32
    @4
    ccrd
    cdm
    wcel
    #
    @9
    @4
    cen
    wbr
    @58
    @46
    @32
    @59
    @50
    @4
    cvv
    onssnum
    mpan
    @4
    cardid2
    @9
    @4
    ensym
    3syl
    @9
    nnsdom
    @4
    @9
    com
    ensdomtr
    syl2an
    @4
    isfinite
    sylibr
    @4
    @19
    wofi
    syl2anc
    sylan
    @4
    @19
    wefr
    syl
    @48
    @45
    @4
    ssid
    a1i
    @14
    @49
    @15
    @0
    @6
    @49
    @13
    @6
    @0
    @49
    @6
    @0
    @4
    c0
    @6
    @4
    c0
    wceq
    #
    cA
    c0
    wceq
    #
    @0
    wn
    #
    @60
    @5
    c0
    wceq
    @6
    @61
    @60
    @5
    c0
    cuni
    c0
    @4
    c0
    unieq
    uni0
    syl6eq
    @5
    cA
    c0
    eqeq1
    syl5ib
    @61
    @0
    c0
    wlim
    #
    nlim0
    cA
    c0
    limeq
    mtbiri
    syl6
    necon2ad
    impcom
    3adant2
    adantr
    vs
    vt
    @4
    @4
    cvv
    @19
    fri
    syl22anc
    mtand
    @9
    con0
    wcel
    #
    @9
    word
    #
    @11
    @16
    wb
    #
    @4
    cardon
    #
    @9
    eloni
    com
    word
    @65
    @66
    ordom
    com
    @9
    ordtri1
    mpan
    mp2b
    sylibr
    syl3an2b
    3expb
    sylan2b
    ralrimiva
    vy
    @8
    @9
    com
    ssiin
    sylibr
    vy
    cA
    cflim2.1
    cflim3
    #
    sseqtr4d
    @0
    @1
    com
    vx
    cv
    #
    wss
    #
    @69
    wlim
    #
    wb
    #
    vx
    cab
    #
    wcel
    @3
    @2
    wb
    #
    @0
    @1
    @69
    @9
    wceq
    #
    vy
    @8
    wrex
    #
    vx
    cab
    #
    cint
    #
    @73
    @0
    @1
    @10
    @78
    @68
    vy
    vx
    @8
    @9
    @4
    ccrd
    fvex
    dfiin2
    syl6eq
    #
    @0
    @77
    @73
    @78
    @76
    @72
    vx
    @75
    @72
    vy
    @8
    @75
    @72
    @11
    @9
    wlim
    #
    wb
    @4
    cardlim
    @75
    @70
    @11
    @71
    @80
    @69
    @9
    com
    sseq2
    @69
    @9
    limeq
    bibi12d
    mpbiri
    rexlimivw
    ss2abi
    @0
    @77
    con0
    wss
    @77
    c0
    wne
    #
    @78
    @77
    wcel
    @76
    vx
    con0
    @75
    @69
    con0
    wcel
    #
    vy
    @8
    @75
    @82
    @64
    @67
    @69
    @9
    con0
    eleq1
    mpbiri
    rexlimivw
    abssi
    @0
    @78
    cvv
    wcel
    @81
    @0
    @78
    @1
    cvv
    @79
    cA
    ccf
    fvex
    #
    syl6eqelr
    @77
    intex
    sylibr
    @77
    onint
    sylancr
    sseldi
    eqeltrd
    @72
    @74
    vx
    @1
    @83
    @69
    @1
    wceq
    @70
    @3
    @71
    @2
    @69
    @1
    com
    sseq2
    @69
    @1
    limeq
    bibi12d
    elab
    sylib
    mpbid
    cA
    con0
    wcel
    #
    @2
    @0
    wi
    @84
    @0
    @2
    @84
    @62
    @61
    cA
    @69
    csuc
    #
    wceq
    #
    vx
    con0
    wrex
    #
    wo
    #
    @2
    wn
    #
    @84
    @61
    @87
    @0
    w3o
    #
    @62
    @88
    wi
    #
    @84
    @33
    @90
    cA
    eloni
    vx
    cA
    ordzsl
    sylib
    @90
    @88
    @0
    wo
    @0
    @88
    wo
    @91
    @61
    @87
    @0
    df-3or
    @88
    @0
    orcom
    @0
    @88
    df-or
    3bitri
    sylib
    @61
    @89
    @87
    @61
    @2
    @63
    nlim0
    @61
    @1
    c0
    wceq
    #
    @2
    @63
    wb
    #
    @61
    @1
    c0
    ccf
    cfv
    c0
    cA
    c0
    ccf
    fveq2
    cf0
    syl6eq
    @1
    c0
    limeq
    #
    syl
    mtbiri
    @86
    @89
    vx
    con0
    @82
    @86
    wa
    #
    @2
    c1o
    wlim
    #
    c1o
    c1o
    cuni
    #
    wne
    @96
    wn
    c1o
    c0
    @97
    1n0
    @97
    c0
    csn
    #
    cuni
    c0
    c1o
    @98
    df1o2
    unieqi
    c0
    0ex
    unisn
    eqtri
    neeqtrri
    @96
    c1o
    @97
    c1o
    limuni
    necon3ai
    ax-mp
    @95
    @1
    c1o
    wceq
    @2
    @96
    wb
    @86
    @82
    @1
    @85
    ccf
    cfv
    c1o
    cA
    @85
    ccf
    fveq2
    @69
    cfsuc
    sylan9eqr
    @1
    c1o
    limeq
    syl
    mtbiri
    rexlimiva
    jaoi
    syl6
    con4d
    @84
    wn
    #
    @2
    @0
    @99
    @2
    @63
    nlim0
    @99
    @92
    @93
    @84
    cA
    ccf
    cdm
    #
    wcel
    @92
    @100
    con0
    cA
    con0
    con0
    ccf
    cff
    fdmi
    eleq2i
    cA
    ccf
    ndmfv
    sylnbir
    @94
    syl
    mtbiri
    pm2.21d
    pm2.61i
    impbii
end
