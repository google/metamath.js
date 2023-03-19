include "cina.mm"
include "wcel.mm"
include "cr1.mm"
include "cfv.mm"
include "cdom.mm"
include "wbr.mm"
include "cen.mm"
include "cxp.mm"
include "cv.mm"
include "ciun.mm"
include "con0.mm"
include "wlim.mm"
include "wceq.mm"
include "cwina.mm"
include "inawina.mm"
include "winaon.mm"
include "syl.mm"
include "winalim.mm"
include "r1lim.mm"
include "syl2anc.mm"
include "wral.mm"
include "wa.mm"
include "csdm.mm"
include "onelon.mm"
include "sylan.mm"
include "wi.mm"
include "c0.mm"
include "csuc.mm"
include "eleq1.mm"
include "fveq2.mm"
include "breq1d.mm"
include "imbi12d.mm"
include "weq.mm"
include "wne.mm"
include "ne0i.mm"
include "0sdomg.mm"
include "syl5ibr.mm"
include "r10.mm"
include "breq1i.mm"
include "syl6ibr.mm"
include "3syl.mm"
include "wtr.mm"
include "word.mm"
include "eloni.mm"
include "ordtr.mm"
include "trsuc.mm"
include "ex.mm"
include "adantl.mm"
include "ccrd.mm"
include "cpw.mm"
include "r1suc.mm"
include "fvex.mm"
include "cardid.mm"
include "ensymi.mm"
include "pwen.mm"
include "ax-mp.mm"
include "syl6eqbr.mm"
include "wb.mm"
include "winacard.mm"
include "eleq2d.mm"
include "cvv.mm"
include "cardsdom.mm"
include "sylancr.mm"
include "bitr3d.mm"
include "ccf.mm"
include "elina.mm"
include "simp3bi.mm"
include "pweq.mm"
include "rspccv.mm"
include "sylbird.mm"
include "imp.mm"
include "ensdomtr.mm"
include "syl2an.mm"
include "expr.mm"
include "imim12d.mm"
include "cun.mm"
include "vex.mm"
include "mpan.mm"
include "nfcv.mm"
include "nfiu1.mm"
include "nfbr.mm"
include "wel.mm"
include "wss.mm"
include "iunex.mm"
include "ssiun2.mm"
include "ssdomg.mm"
include "mpsyl.mm"
include "endomtr.mm"
include "vtoclgaf.mm"
include "rgen.mm"
include "iundom.mm"
include "mp2an.mm"
include "unex.mm"
include "ssun2.mm"
include "mp2.mm"
include "xpdom2.mm"
include "ssun1.mm"
include "xpdom1.mm"
include "domtr.mm"
include "com.mm"
include "limomss.mm"
include "syl6ss.mm"
include "infxpidm.mm"
include "domentr.mm"
include "eqbrtrd.mm"
include "ad2antlr.mm"
include "wn.mm"
include "eleq1a.mm"
include "ordirr.mm"
include "nsyli.mm"
include "ad2ant2r.mm"
include "simpll.mm"
include "wf.mm"
include "wrex.mm"
include "wex.mm"
include "ccom.mm"
include "cres.mm"
include "wfn.mm"
include "limord.mm"
include "elon.mm"
include "sylibr.mm"
include "cardf.mm"
include "r1fnon.mm"
include "dffn2.mm"
include "mpbi.mm"
include "fco.mm"
include "onss.mm"
include "fssres.mm"
include "ffn.mm"
include "simpr.mm"
include "simplll.mm"
include "ontr1.mm"
include "syl12anc.mm"
include "biimpd.mm"
include "embantd.mm"
include "fvres.mm"
include "fvco3.mm"
include "eqtrd.mm"
include "eleq1d.mm"
include "sylibrd.mm"
include "ralimdva.mm"
include "impr.mm"
include "ffnfv.mm"
include "sylanbrc.mm"
include "eleq2.mm"
include "biimpa.mm"
include "eliun.mm"
include "cardon.mm"
include "onelssi.mm"
include "sseq2d.mm"
include "reximdva.mm"
include "syl5bi.mm"
include "syl5.mm"
include "expdimp.mm"
include "ralrimiv.mm"
include "wfun.mm"
include "ffun.mm"
include "resfunexg.mm"
include "feq1.mm"
include "fveq1.mm"
include "rexbidv.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "spcev.mm"
include "syl6an.mm"
include "ad2antrl.mm"
include "cfflb.mm"
include "syld.mm"
include "simp2bi.mm"
include "sseq1d.mm"
include "sylibd.mm"
include "ontri1.mm"
include "mt2d.mm"
include "wo.mm"
include "iunon.mm"
include "a1i.mm"
include "mprg.mm"
include "eqcom.mm"
include "ordequn.mm"
include "sylancl.mm"
include "mtord.mm"
include "onelss.mm"
include "sylc.mm"
include "sylsyld.mm"
include "iunss.mm"
include "unssd.mm"
include "cif.mm"
include "id.mm"
include "iuneq1.mm"
include "uneq12d.mm"
include "0elon.mm"
include "elimel.mm"
include "elexi.mm"
include "onun2i.mm"
include "dedth.mm"
include "adantr.mm"
include "onsseleq.mm"
include "mpbid.mm"
include "orcomd.mm"
include "ord.mm"
include "mpd.mm"
include "iscard.mm"
include "simprbi.mm"
include "breq1.mm"
include "domsdomtr.mm"
include "exp43.mm"
include "com4l.mm"
include "tfinds2.mm"
include "impd.mm"
include "mpcom.mm"
include "sdomdom.mm"
include "ralrimiva.mm"
include "winainf.mm"
include "infxpen.mm"
include "cdm.mm"
include "fdmi.mm"
include "syl6eleqr.mm"
include "onssr1.mm"
include "sbth.mm"

theorem inar1
  let cA: class A
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A e. Inacc -> ( R1 ` A ) ~~ A )

  proof
    cA
    cina
    wcel
    #
    cA
    cr1
    cfv
    #
    cA
    cdom
    wbr
    #
    cA
    @1
    cdom
    wbr
    #
    @1
    cA
    cen
    wbr
    @0
    @1
    cA
    cA
    cxp
    #
    cdom
    wbr
    @4
    cA
    cen
    wbr
    #
    @2
    @0
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
    @4
    cdom
    @0
    cA
    con0
    wcel
    #
    cA
    wlim
    #
    @1
    @8
    wceq
    @0
    cA
    cwina
    wcel
    #
    @9
    cA
    inawina
    #
    cA
    winaon
    #
    syl
    #
    @0
    @11
    @10
    @12
    cA
    winalim
    syl
    vx
    cA
    con0
    r1lim
    syl2anc
    @0
    @9
    @7
    cA
    cdom
    wbr
    #
    vx
    cA
    wral
    @8
    @4
    cdom
    wbr
    @14
    @0
    @15
    vx
    cA
    @0
    @6
    cA
    wcel
    #
    wa
    #
    @7
    cA
    csdm
    wbr
    #
    @15
    @6
    con0
    wcel
    #
    @17
    @18
    @0
    @9
    @16
    @19
    @14
    cA
    @6
    onelon
    sylan
    @19
    @0
    @16
    @18
    @16
    @18
    wi
    c0
    cA
    wcel
    #
    c0
    cr1
    cfv
    #
    cA
    csdm
    wbr
    #
    wi
    #
    vy
    cv
    #
    cA
    wcel
    #
    @24
    cr1
    cfv
    #
    cA
    csdm
    wbr
    #
    wi
    #
    @24
    csuc
    #
    cA
    wcel
    #
    @29
    cr1
    cfv
    #
    cA
    csdm
    wbr
    #
    wi
    #
    @0
    vx
    vy
    @6
    c0
    wceq
    #
    @16
    @20
    @18
    @22
    @6
    c0
    cA
    eleq1
    @34
    @7
    @21
    cA
    csdm
    @6
    c0
    cr1
    fveq2
    breq1d
    imbi12d
    vx
    vy
    weq
    #
    @16
    @25
    @18
    @27
    @6
    @24
    cA
    eleq1
    @35
    @7
    @26
    cA
    csdm
    @6
    @24
    cr1
    fveq2
    breq1d
    imbi12d
    @6
    @29
    wceq
    #
    @16
    @30
    @18
    @32
    @6
    @29
    cA
    eleq1
    @36
    @7
    @31
    cA
    csdm
    @6
    @29
    cr1
    fveq2
    breq1d
    imbi12d
    @0
    @11
    @9
    @23
    @12
    @13
    @9
    @20
    c0
    cA
    csdm
    wbr
    #
    @22
    @20
    @37
    @9
    cA
    c0
    wne
    #
    cA
    c0
    ne0i
    cA
    con0
    0sdomg
    syl5ibr
    @21
    c0
    cA
    csdm
    r10
    breq1i
    syl6ibr
    3syl
    @24
    con0
    wcel
    #
    @0
    @28
    @33
    wi
    @39
    @0
    wa
    @30
    @25
    @27
    @32
    @0
    @30
    @25
    wi
    #
    @39
    @0
    @9
    cA
    wtr
    #
    @40
    @14
    @9
    cA
    word
    #
    @41
    cA
    eloni
    #
    cA
    ordtr
    syl
    @41
    @30
    @25
    cA
    @24
    trsuc
    ex
    3syl
    adantl
    @39
    @0
    @27
    @32
    @39
    @31
    @26
    ccrd
    cfv
    #
    cpw
    #
    cen
    wbr
    @45
    cA
    csdm
    wbr
    #
    @32
    @0
    @27
    wa
    @39
    @31
    @26
    cpw
    #
    @45
    cen
    @24
    r1suc
    @26
    @44
    cen
    wbr
    #
    @47
    @45
    cen
    wbr
    @44
    @26
    @26
    @24
    cr1
    fvex
    #
    cardid
    ensymi
    #
    @26
    @44
    pwen
    ax-mp
    syl6eqbr
    @0
    @27
    @46
    @0
    @27
    @44
    cA
    wcel
    #
    @46
    @0
    @11
    @51
    @27
    wb
    @12
    @11
    @44
    cA
    ccrd
    cfv
    #
    wcel
    #
    @51
    @27
    @11
    @52
    cA
    @44
    cA
    winacard
    #
    eleq2d
    @11
    @26
    cvv
    wcel
    #
    @9
    @53
    @27
    wb
    #
    @49
    @13
    @26
    cA
    cvv
    con0
    cardsdom
    #
    sylancr
    bitr3d
    syl
    @0
    vz
    cv
    #
    cpw
    #
    cA
    csdm
    wbr
    #
    vz
    cA
    wral
    #
    @51
    @46
    wi
    @0
    @38
    cA
    ccf
    cfv
    #
    cA
    wceq
    #
    @61
    vz
    cA
    elina
    #
    simp3bi
    @60
    @46
    vz
    @44
    cA
    @58
    @44
    wceq
    @59
    @45
    cA
    csdm
    @58
    @44
    pweq
    breq1d
    rspccv
    syl
    sylbird
    imp
    @31
    @45
    cA
    ensdomtr
    syl2an
    expr
    imim12d
    ex
    @16
    @6
    wlim
    #
    @0
    @28
    vy
    @6
    wral
    #
    @18
    @16
    @65
    @0
    @66
    @18
    @16
    @65
    wa
    #
    @0
    @66
    wa
    #
    wa
    #
    @7
    @6
    vy
    @6
    @44
    ciun
    #
    cun
    #
    cdom
    wbr
    #
    @71
    cA
    csdm
    wbr
    #
    @18
    @65
    @72
    @16
    @68
    @65
    @7
    vz
    @6
    @58
    cr1
    cfv
    #
    ciun
    #
    @71
    cdom
    @6
    cvv
    wcel
    #
    @65
    @7
    @75
    wceq
    vx
    vex
    #
    vz
    @6
    cvv
    r1lim
    mpan
    @65
    @75
    @6
    @70
    cxp
    #
    cdom
    wbr
    #
    @78
    @71
    cdom
    wbr
    #
    @75
    @71
    cdom
    wbr
    @76
    @74
    @70
    cdom
    wbr
    #
    vz
    @6
    wral
    @79
    @77
    @81
    vz
    @6
    @26
    @70
    cdom
    wbr
    #
    @81
    vy
    @58
    @6
    vy
    @58
    nfcv
    vy
    @74
    @70
    cdom
    vy
    @74
    nfcv
    vy
    cdom
    nfcv
    vy
    @6
    @44
    nfiu1
    nfbr
    vy
    vz
    weq
    @26
    @74
    @70
    cdom
    @24
    @58
    cr1
    fveq2
    breq1d
    vy
    vx
    wel
    #
    @48
    @44
    @70
    cdom
    wbr
    #
    @82
    @50
    @70
    cvv
    wcel
    @83
    @44
    @70
    wss
    @84
    vy
    @6
    @44
    @77
    @26
    ccrd
    fvex
    iunex
    #
    vy
    @6
    @44
    ssiun2
    @44
    @70
    cvv
    ssdomg
    mpsyl
    @26
    @44
    @70
    endomtr
    sylancr
    vtoclgaf
    rgen
    vz
    @6
    @70
    @74
    cvv
    iundom
    mp2an
    @65
    @78
    @71
    @71
    cxp
    #
    cdom
    wbr
    #
    @86
    @71
    cen
    wbr
    #
    @80
    @78
    @6
    @71
    cxp
    #
    cdom
    wbr
    #
    @89
    @86
    cdom
    wbr
    #
    @87
    @70
    @71
    cdom
    wbr
    #
    @90
    @71
    cvv
    wcel
    #
    @70
    @71
    wss
    @92
    @6
    @70
    @77
    @85
    unex
    #
    @70
    @6
    ssun2
    @70
    @71
    cvv
    ssdomg
    mp2
    @70
    @71
    @6
    @77
    xpdom2
    ax-mp
    @6
    @71
    cdom
    wbr
    #
    @91
    @93
    @6
    @71
    wss
    @95
    @94
    @6
    @70
    ssun1
    #
    @6
    @71
    cvv
    ssdomg
    mp2
    @6
    @71
    @71
    @94
    xpdom1
    ax-mp
    @78
    @89
    @86
    domtr
    mp2an
    @65
    com
    @71
    cdom
    wbr
    #
    @88
    @93
    @65
    com
    @71
    wss
    @97
    @94
    @65
    com
    @6
    @71
    @6
    limomss
    @96
    syl6ss
    com
    @71
    cvv
    ssdomg
    mpsyl
    @71
    infxpidm
    syl
    @78
    @86
    @71
    domentr
    sylancr
    @75
    @78
    @71
    domtr
    sylancr
    eqbrtrd
    ad2antlr
    @69
    @71
    cA
    wcel
    #
    @73
    @69
    @71
    cA
    wceq
    #
    wn
    @98
    @69
    @99
    cA
    @6
    wceq
    #
    cA
    @70
    wceq
    #
    @16
    @0
    @100
    wn
    #
    @65
    @66
    @16
    @0
    @102
    @16
    @100
    cA
    cA
    wcel
    #
    @0
    @6
    cA
    cA
    eleq1a
    @0
    @9
    @42
    @103
    wn
    @14
    @43
    cA
    ordirr
    3syl
    nsyli
    imp
    ad2ant2r
    @69
    @101
    @16
    @16
    @65
    @68
    simpll
    #
    @69
    @101
    cA
    @6
    wss
    #
    @16
    wn
    #
    @69
    @101
    @62
    @6
    wss
    #
    @105
    @69
    @101
    @6
    cA
    vw
    cv
    #
    wf
    #
    @58
    @24
    @108
    cfv
    #
    wss
    #
    vy
    @6
    wrex
    #
    vz
    cA
    wral
    #
    wa
    #
    vw
    wex
    #
    @107
    @69
    @6
    cA
    ccrd
    cr1
    ccom
    #
    @6
    cres
    #
    wf
    #
    @101
    @58
    @24
    @117
    cfv
    #
    wss
    #
    vy
    @6
    wrex
    #
    vz
    cA
    wral
    #
    @115
    @69
    @117
    @6
    wfn
    #
    @119
    cA
    wcel
    #
    vy
    @6
    wral
    #
    @118
    @69
    @19
    @6
    con0
    @117
    wf
    #
    @123
    @65
    @19
    @16
    @68
    @65
    @6
    word
    #
    @19
    @6
    limord
    @6
    @77
    elon
    sylibr
    #
    ad2antlr
    #
    @19
    con0
    con0
    @116
    wf
    #
    @6
    con0
    wss
    @126
    cvv
    con0
    ccrd
    wf
    con0
    cvv
    cr1
    wf
    #
    @130
    cardf
    cr1
    con0
    wfn
    @131
    r1fnon
    con0
    cr1
    dffn2
    mpbi
    #
    con0
    cvv
    con0
    ccrd
    cr1
    fco
    mp2an
    #
    @6
    onss
    con0
    con0
    @6
    @116
    fssres
    sylancr
    @6
    con0
    @117
    ffn
    3syl
    @67
    @0
    @66
    @125
    @67
    @0
    wa
    #
    @28
    @124
    vy
    @6
    @134
    @83
    wa
    #
    @28
    @51
    @124
    @135
    @25
    @27
    @51
    @135
    @9
    @83
    @16
    @25
    @0
    @9
    @67
    @83
    @14
    ad2antlr
    #
    @134
    @83
    simpr
    @16
    @65
    @0
    @83
    simplll
    @9
    @83
    @16
    wa
    @25
    @24
    @6
    cA
    ontr1
    imp
    syl12anc
    @135
    @27
    @51
    @135
    @53
    @27
    @51
    @135
    @55
    @9
    @56
    @49
    @136
    @57
    sylancr
    @135
    @52
    cA
    @44
    @0
    @52
    cA
    wceq
    #
    @67
    @83
    @0
    @11
    @137
    @12
    @54
    syl
    #
    ad2antlr
    eleq2d
    bitr3d
    biimpd
    embantd
    #
    @135
    @119
    @44
    cA
    @134
    @19
    @83
    @119
    @44
    wceq
    @65
    @19
    @16
    @0
    @128
    ad2antlr
    @19
    @83
    wa
    #
    @119
    @24
    @116
    cfv
    #
    @44
    @83
    @119
    @141
    wceq
    @19
    @24
    @6
    @116
    fvres
    adantl
    @140
    @131
    @39
    @141
    @44
    wceq
    @132
    @6
    @24
    onelon
    con0
    cvv
    @24
    ccrd
    cr1
    fvco3
    sylancr
    eqtrd
    #
    sylan
    eleq1d
    sylibrd
    ralimdva
    impr
    vy
    @6
    cA
    @117
    ffnfv
    sylanbrc
    @69
    @19
    @101
    @122
    wi
    @129
    @19
    @101
    @122
    @19
    @101
    wa
    @121
    vz
    cA
    @19
    @101
    @58
    cA
    wcel
    #
    @121
    @101
    @143
    wa
    @58
    @70
    wcel
    #
    @19
    @121
    @101
    @143
    @144
    cA
    @70
    @58
    eleq2
    biimpa
    @144
    @58
    @44
    wcel
    #
    vy
    @6
    wrex
    @19
    @121
    vy
    @58
    @6
    @44
    eliun
    @19
    @145
    @120
    vy
    @6
    @145
    @120
    @140
    @58
    @44
    wss
    @44
    @58
    @26
    cardon
    #
    onelssi
    @140
    @119
    @44
    @58
    @142
    sseq2d
    syl5ibr
    reximdva
    syl5bi
    syl5
    expdimp
    ralrimiv
    ex
    syl
    @114
    @118
    @122
    wa
    vw
    @117
    @116
    wfun
    #
    @76
    @117
    cvv
    wcel
    @130
    @147
    @133
    con0
    con0
    @116
    ffun
    ax-mp
    @77
    @116
    @6
    cvv
    resfunexg
    mp2an
    @108
    @117
    wceq
    #
    @109
    @118
    @113
    @122
    @6
    cA
    @108
    @117
    feq1
    @148
    @112
    @121
    vz
    cA
    @148
    @111
    @120
    vy
    @6
    @148
    @110
    @119
    @58
    @24
    @108
    @117
    fveq1
    sseq2d
    rexbidv
    ralbidv
    anbi12d
    spcev
    syl6an
    @69
    @9
    @19
    @115
    @107
    wi
    @0
    @9
    @67
    @66
    @14
    ad2antrl
    #
    @129
    vz
    vy
    cA
    @6
    vw
    cfflb
    syl2anc
    syld
    @0
    @107
    @105
    wb
    @67
    @66
    @0
    @62
    cA
    @6
    @0
    @38
    @63
    @61
    @64
    simp2bi
    sseq1d
    ad2antrl
    sylibd
    @69
    @9
    @19
    @105
    @106
    wb
    @149
    @129
    cA
    @6
    ontri1
    syl2anc
    sylibd
    mt2d
    @69
    @19
    @70
    con0
    wcel
    #
    @99
    @100
    @101
    wo
    #
    wi
    @129
    @44
    con0
    wcel
    #
    @150
    vy
    @6
    @76
    @152
    vy
    @6
    wral
    @150
    @77
    vy
    @6
    @44
    cvv
    iunon
    mpan
    @152
    @83
    @146
    a1i
    mprg
    @99
    cA
    @71
    wceq
    #
    @19
    @150
    wa
    @151
    @71
    cA
    eqcom
    @19
    @127
    @70
    word
    @153
    @151
    wi
    @150
    @6
    eloni
    @70
    eloni
    cA
    @6
    @70
    ordequn
    syl2an
    syl5bi
    sylancl
    mtord
    @69
    @99
    @98
    @69
    @98
    @99
    @69
    @71
    cA
    wss
    #
    @98
    @99
    wo
    #
    @69
    @6
    @70
    cA
    @69
    @9
    @16
    @6
    cA
    wss
    @149
    @104
    cA
    @6
    onelss
    sylc
    @69
    @44
    cA
    wss
    #
    vy
    @6
    wral
    #
    @70
    cA
    wss
    @67
    @0
    @66
    @157
    @134
    @28
    @156
    vy
    @6
    @135
    @9
    @28
    @51
    @156
    @136
    @139
    cA
    @44
    onelss
    sylsyld
    ralimdva
    impr
    vy
    @6
    @44
    cA
    iunss
    sylibr
    unssd
    @67
    @71
    con0
    wcel
    #
    @9
    @154
    @155
    wb
    @68
    @65
    @158
    @16
    @65
    @19
    @158
    @128
    @19
    @158
    @19
    @6
    c0
    cif
    #
    vy
    @159
    @44
    ciun
    #
    cun
    #
    con0
    wcel
    @6
    c0
    @6
    @159
    wceq
    #
    @71
    @161
    con0
    @162
    @6
    @159
    @70
    @160
    @162
    id
    vy
    @6
    @159
    @44
    iuneq1
    uneq12d
    eleq1d
    @159
    @160
    @6
    c0
    con0
    0elon
    elimel
    #
    @152
    @160
    con0
    wcel
    #
    vy
    @159
    @159
    cvv
    wcel
    @152
    vy
    @159
    wral
    @164
    @159
    con0
    @163
    elexi
    vy
    @159
    @44
    cvv
    iunon
    mpan
    @152
    @24
    @159
    wcel
    @146
    a1i
    mprg
    onun2i
    dedth
    syl
    adantl
    @0
    @9
    @66
    @14
    adantr
    @71
    cA
    onsseleq
    syl2an
    mpbid
    orcomd
    ord
    mpd
    @69
    @137
    @58
    cA
    csdm
    wbr
    #
    vz
    cA
    wral
    #
    @98
    @73
    wi
    @0
    @137
    @67
    @66
    @138
    ad2antrl
    @137
    @9
    @166
    vz
    cA
    iscard
    simprbi
    @165
    @73
    vz
    @71
    cA
    @58
    @71
    cA
    csdm
    breq1
    rspccv
    3syl
    mpd
    @7
    @71
    cA
    domsdomtr
    syl2anc
    exp43
    com4l
    tfinds2
    impd
    mpcom
    @7
    cA
    sdomdom
    syl
    ralrimiva
    vx
    cA
    cA
    @7
    con0
    iundom
    syl2anc
    eqbrtrd
    @0
    @9
    com
    cA
    wss
    #
    @5
    @14
    @0
    @11
    @167
    @12
    cA
    winainf
    syl
    cA
    infxpen
    syl2anc
    @1
    @4
    cA
    domentr
    syl2anc
    @1
    cvv
    wcel
    @0
    cA
    @1
    wss
    #
    @3
    cA
    cr1
    fvex
    @0
    @11
    cA
    cr1
    cdm
    #
    wcel
    @168
    @12
    @11
    cA
    con0
    @169
    @13
    con0
    cvv
    cr1
    @132
    fdmi
    syl6eleqr
    cA
    onssr1
    3syl
    cA
    @1
    cvv
    ssdomg
    mpsyl
    @1
    cA
    sbth
    syl2anc
end
