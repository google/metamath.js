include "cfin2.mm"
include "wcel.mm"
include "wor.mm"
include "ccrd.mm"
include "cdm.mm"
include "cfn.mm"
include "wa.mm"
include "cv.mm"
include "wwe.mm"
include "wex.mm"
include "cxp.mm"
include "cin.mm"
include "wfr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "wal.mm"
include "crab.mm"
include "cmpt.mm"
include "crn.mm"
include "cint.mm"
include "wceq.mm"
include "cpw.mm"
include "crpss.mm"
include "simplll.mm"
include "ssrab2.mm"
include "sstr.mm"
include "mpan.mm"
include "elpw2g.mm"
include "biimpar.mm"
include "sylan2.mm"
include "ralrimivw.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "rabex.mm"
include "rgenw.mm"
include "eqid.mm"
include "eleq1.mm"
include "ralrnmpt.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "dfss3.mm"
include "adantlr.mm"
include "adantr.mm"
include "dmmpti.mm"
include "neeq1i.mm"
include "dm0rn0.mm"
include "necon3bii.mm"
include "sylbb1.mm"
include "adantl.mm"
include "soss.mm"
include "impcom.mm"
include "wpo.mm"
include "porpss.mm"
include "a1i.mm"
include "weq.mm"
include "w3o.mm"
include "wel.mm"
include "solin.mm"
include "fin2solem.mm"
include "breq2.mm"
include "rabbidv.mm"
include "ancom2s.mm"
include "3orim123d.mm"
include "mpd.mm"
include "ralrimivva.mm"
include "breq1.mm"
include "eqeq1.mm"
include "3orbi123d.mm"
include "ralbidv.mm"
include "r19.21bi.mm"
include "cbvmptv.mm"
include "eqeq2.mm"
include "anasss.mm"
include "issod.mm"
include "syl.mm"
include "adantll.mm"
include "fin2i2.mm"
include "syl22anc.mm"
include "elrnmpti.mm"
include "sylib.mm"
include "ssel2.mm"
include "sonr.mm"
include "anassrs.mm"
include "elrab.mm"
include "simplbi2.mm"
include "ad2antlr.mm"
include "elint2.mm"
include "eleq2.mm"
include "bitri.mm"
include "eleq2d.mm"
include "rspcv.mm"
include "simprbi.mm"
include "syl6.mm"
include "syl5bi.mm"
include "imbi1d.mm"
include "syl5ibcom.mm"
include "imp.mm"
include "syld.mm"
include "adantlll.mm"
include "mtod.mm"
include "ex.mm"
include "ralrimdva.mm"
include "reximdva.mm"
include "expl.mm"
include "alrimiv.mm"
include "df-fr.mm"
include "simpr.mm"
include "df-we.mm"
include "sylanbrc.mm"
include "weinxp.mm"
include "sqxpexg.mm"
include "incom.mm"
include "inex1g.mm"
include "syl5eqel.mm"
include "weeq1.mm"
include "spcegv.mm"
include "3syl.mm"
include "syldan.mm"
include "ween.mm"
include "cfin7.mm"
include "cfin5.mm"
include "cfin6.mm"
include "cfin3.mm"
include "cfin4.mm"
include "fin23.mm"
include "fin34.mm"
include "fin45.mm"
include "fin56.mm"
include "fin67.mm"
include "fin71num.mm"
include "biimpac.mm"
include "sylan.mm"

theorem fin2so
  let cA: class A
  let cR: class R
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. Fin2 /\ R Or A ) -> A e. Fin )

  proof
    cA
    cfin2
    wcel
    #
    cA
    cR
    wor
    #
    cA
    ccrd
    cdm
    wcel
    #
    cA
    cfn
    wcel
    #
    @0
    @1
    wa
    #
    cA
    vz
    cv
    #
    wwe
    #
    vz
    wex
    #
    @2
    @0
    @1
    cA
    cR
    cA
    cA
    cxp
    #
    cin
    #
    wwe
    #
    @7
    @4
    cA
    cR
    wwe
    #
    @10
    @4
    cA
    cR
    wfr
    #
    @1
    @11
    @4
    vx
    cv
    #
    cA
    wss
    #
    @13
    c0
    wne
    #
    wa
    @5
    vy
    cv
    #
    cR
    wbr
    #
    wn
    #
    vz
    @13
    wral
    #
    vy
    @13
    wrex
    #
    wi
    #
    vx
    wal
    @12
    @4
    @21
    vx
    @4
    @14
    @15
    @20
    @4
    @14
    wa
    #
    @15
    wa
    #
    vv
    @13
    vw
    cv
    #
    vv
    cv
    #
    cR
    wbr
    #
    vw
    @13
    crab
    #
    cmpt
    #
    crn
    #
    cint
    #
    @24
    @16
    cR
    wbr
    #
    vw
    @13
    crab
    #
    wceq
    #
    vy
    @13
    wrex
    #
    @20
    @23
    @30
    @29
    wcel
    #
    @34
    @23
    @0
    @29
    cA
    cpw
    #
    wss
    #
    @29
    c0
    wne
    #
    @29
    crpss
    wor
    #
    @35
    @0
    @1
    @14
    @15
    simplll
    @22
    @37
    @15
    @0
    @14
    @37
    @1
    @0
    @14
    wa
    #
    @16
    @36
    wcel
    #
    vy
    @29
    wral
    #
    @37
    @40
    @27
    @36
    wcel
    #
    vv
    @13
    wral
    #
    @42
    @40
    @43
    vv
    @13
    @14
    @0
    @27
    cA
    wss
    #
    @43
    @27
    @13
    wss
    @14
    @45
    @26
    vw
    @13
    ssrab2
    @27
    @13
    cA
    sstr
    mpan
    @0
    @43
    @45
    @27
    cA
    cfin2
    elpw2g
    biimpar
    sylan2
    ralrimivw
    @27
    cvv
    wcel
    #
    vv
    @13
    wral
    #
    @42
    @44
    wb
    @46
    vv
    @13
    @26
    vw
    @13
    vx
    vex
    #
    rabex
    #
    rgenw
    #
    @41
    @43
    vv
    vy
    @13
    @27
    @28
    cvv
    @28
    eqid
    #
    @16
    @27
    @36
    eleq1
    ralrnmpt
    ax-mp
    sylibr
    vy
    @29
    @36
    dfss3
    sylibr
    adantlr
    adantr
    @15
    @38
    @22
    @28
    cdm
    #
    c0
    wne
    @15
    @38
    @52
    @13
    c0
    vv
    @13
    @27
    @28
    @49
    @51
    dmmpti
    neeq1i
    @52
    c0
    @29
    c0
    @28
    dm0rn0
    necon3bii
    sylbb1
    adantl
    @22
    @39
    @15
    @1
    @14
    @39
    @0
    @1
    @14
    wa
    #
    @13
    cR
    wor
    #
    @39
    @14
    @1
    @54
    @13
    cA
    cR
    soss
    impcom
    @54
    vu
    vz
    @29
    crpss
    @29
    crpss
    wpo
    @54
    @29
    porpss
    a1i
    @54
    vu
    cv
    #
    @29
    wcel
    #
    @5
    @29
    wcel
    @55
    @5
    crpss
    wbr
    #
    vu
    vz
    weq
    #
    @5
    @55
    crpss
    wbr
    #
    w3o
    #
    @54
    @56
    wa
    #
    @60
    vz
    @29
    @61
    @55
    @32
    crpss
    wbr
    #
    @55
    @32
    wceq
    #
    @32
    @55
    crpss
    wbr
    #
    w3o
    #
    vy
    @13
    wral
    #
    @60
    vz
    @29
    wral
    #
    @54
    @66
    vu
    @29
    @54
    @27
    @32
    crpss
    wbr
    #
    @27
    @32
    wceq
    #
    @32
    @27
    crpss
    wbr
    #
    w3o
    #
    vy
    @13
    wral
    #
    vv
    @13
    wral
    #
    @66
    vu
    @29
    wral
    #
    @54
    @71
    vv
    vy
    @13
    @13
    @54
    vv
    vx
    wel
    #
    vy
    vx
    wel
    #
    wa
    wa
    #
    @25
    @16
    cR
    wbr
    #
    vv
    vy
    weq
    #
    @16
    @25
    cR
    wbr
    #
    w3o
    @71
    @13
    @25
    @16
    cR
    solin
    @77
    @78
    @68
    @79
    @69
    @80
    @70
    vx
    vv
    vy
    vw
    cR
    fin2solem
    @79
    @69
    wi
    @77
    @79
    @26
    @31
    vw
    @13
    @25
    @16
    @24
    cR
    breq2
    rabbidv
    #
    a1i
    @54
    @76
    @75
    @80
    @70
    wi
    vx
    vy
    vv
    vw
    cR
    fin2solem
    ancom2s
    3orim123d
    mpd
    ralrimivva
    @47
    @74
    @73
    wb
    @50
    @66
    @72
    vv
    vu
    @13
    @27
    @28
    cvv
    @51
    @55
    @27
    wceq
    #
    @65
    @71
    vy
    @13
    @82
    @62
    @68
    @63
    @69
    @64
    @70
    @55
    @27
    @32
    crpss
    breq1
    @55
    @27
    @32
    eqeq1
    @55
    @27
    @32
    crpss
    breq2
    3orbi123d
    ralbidv
    ralrnmpt
    ax-mp
    sylibr
    r19.21bi
    @32
    cvv
    wcel
    #
    vy
    @13
    wral
    @67
    @66
    wb
    @83
    vy
    @13
    @31
    vw
    @13
    @48
    rabex
    #
    rgenw
    @60
    @65
    vy
    vz
    @13
    @32
    @28
    cvv
    vv
    vy
    @13
    @27
    @32
    @81
    cbvmptv
    #
    @5
    @32
    wceq
    @57
    @62
    @58
    @63
    @59
    @64
    @5
    @32
    @55
    crpss
    breq2
    @5
    @32
    @55
    eqeq2
    @5
    @32
    @55
    crpss
    breq1
    3orbi123d
    ralrnmpt
    ax-mp
    sylibr
    r19.21bi
    anasss
    issod
    syl
    adantll
    adantr
    cA
    @29
    fin2i2
    syl22anc
    vy
    @13
    @32
    @30
    @28
    @85
    @84
    elrnmpti
    sylib
    @22
    @34
    @20
    wi
    #
    @15
    @1
    @14
    @86
    @0
    @53
    @33
    @19
    vy
    @13
    @53
    @76
    wa
    #
    @33
    @18
    vz
    @13
    @87
    vz
    vx
    wel
    #
    wa
    #
    @33
    @18
    @89
    @33
    wa
    @17
    @5
    @5
    cR
    wbr
    #
    @89
    @90
    wn
    #
    @33
    @53
    @88
    @91
    @76
    @1
    @14
    @88
    @91
    @14
    @88
    wa
    @1
    @5
    cA
    wcel
    @91
    @13
    cA
    @5
    ssel2
    cA
    @5
    cR
    sonr
    sylan2
    anassrs
    adantlr
    adantr
    @76
    @88
    @33
    @17
    @90
    wi
    @53
    @76
    @88
    wa
    #
    @33
    wa
    @17
    @5
    @32
    wcel
    #
    @90
    @88
    @17
    @93
    wi
    @76
    @33
    @93
    @88
    @17
    @31
    @17
    vw
    @5
    @13
    @24
    @5
    @16
    cR
    breq1
    elrab
    simplbi2
    ad2antlr
    @92
    @33
    @93
    @90
    wi
    #
    @92
    @5
    @30
    wcel
    #
    @90
    wi
    @33
    @94
    @95
    @5
    @27
    wcel
    #
    vv
    @13
    wral
    #
    @92
    @90
    @95
    vz
    vy
    wel
    #
    vy
    @29
    wral
    #
    @97
    vy
    @5
    @29
    vz
    vex
    elint2
    @47
    @99
    @97
    wb
    @50
    @98
    @96
    vv
    vy
    @13
    @27
    @28
    cvv
    @51
    @16
    @27
    @5
    eleq2
    ralrnmpt
    ax-mp
    bitri
    @88
    @97
    @90
    wi
    @76
    @88
    @97
    @5
    @24
    @5
    cR
    wbr
    #
    vw
    @13
    crab
    #
    wcel
    #
    @90
    @96
    @102
    vv
    @5
    @13
    vv
    vz
    weq
    #
    @27
    @101
    @5
    @103
    @26
    @100
    vw
    @13
    @25
    @5
    @24
    cR
    breq2
    rabbidv
    eleq2d
    rspcv
    @102
    @88
    @90
    @100
    @90
    vw
    @5
    @13
    @24
    @5
    @5
    cR
    breq1
    elrab
    simprbi
    syl6
    adantl
    syl5bi
    @33
    @95
    @93
    @90
    @30
    @32
    @5
    eleq2
    imbi1d
    syl5ibcom
    imp
    syld
    adantlll
    mtod
    ex
    ralrimdva
    reximdva
    adantll
    adantr
    mpd
    expl
    alrimiv
    vx
    vy
    vz
    cA
    cR
    df-fr
    sylibr
    @0
    @1
    simpr
    cA
    cR
    df-we
    sylanbrc
    cA
    cR
    weinxp
    sylib
    @0
    @10
    @7
    @0
    @8
    cvv
    wcel
    #
    @9
    cvv
    wcel
    @10
    @7
    wi
    cA
    cfin2
    sqxpexg
    @104
    @9
    @8
    cR
    cin
    cvv
    cR
    @8
    incom
    @8
    cR
    cvv
    inex1g
    syl5eqel
    @6
    @10
    vz
    @9
    cvv
    cA
    @5
    @9
    weeq1
    spcegv
    3syl
    imp
    syldan
    cA
    vz
    ween
    sylibr
    @0
    cA
    cfin7
    wcel
    #
    @2
    @3
    @0
    cA
    cfin5
    wcel
    #
    cA
    cfin6
    wcel
    @105
    @0
    cA
    cfin3
    wcel
    cA
    cfin4
    wcel
    @106
    cA
    fin23
    cA
    fin34
    cA
    fin45
    3syl
    cA
    fin56
    cA
    fin67
    3syl
    @2
    @105
    @3
    cA
    fin71num
    biimpac
    sylan
    syldan
end
