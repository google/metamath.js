include "wcel.mm"
include "cv.mm"
include "cslt.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wa.mm"
include "csur.mm"
include "wss.mm"
include "cvv.mm"
include "w3a.mm"
include "cdm.mm"
include "csuc.mm"
include "cres.mm"
include "c2o.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "simp1l.mm"
include "simp3.mm"
include "breq1.mm"
include "rspcv.mm"
include "sylc.mm"
include "cfv.mm"
include "wne.mm"
include "con0.mm"
include "crab.mm"
include "cint.mm"
include "simpl21.mm"
include "simpl1l.mm"
include "sseldd.mm"
include "simpl23.mm"
include "wceq.mm"
include "simp21.mm"
include "wor.mm"
include "sltso.mm"
include "sonr.mm"
include "mpan.mm"
include "syl.mm"
include "breq2.mm"
include "notbid.mm"
include "syl5ibcom.mm"
include "con2d.mm"
include "imp.mm"
include "neqned.mm"
include "nosepssdm.mm"
include "syl3anc.mm"
include "wo.mm"
include "wb.mm"
include "nosepon.mm"
include "nodmon.mm"
include "onsseleq.mm"
include "syl2anc.mm"
include "c1o.mm"
include "c0.mm"
include "ctp.mm"
include "wrex.mm"
include "adantr.mm"
include "onelon.mm"
include "sylan.mm"
include "simpr.mm"
include "weq.mm"
include "fveq2.mm"
include "neeq12d.mm"
include "onnminsb.mm"
include "df-ne.mm"
include "con2bii.mm"
include "sylibr.mm"
include "simplr.mm"
include "wi.mm"
include "ontr1.mm"
include "mp2and.mm"
include "fvresd.mm"
include "eqtr4d.mm"
include "ralrimiva.mm"
include "sltval2.mm"
include "mpbid.mm"
include "breqtrrd.mm"
include "raleq.mm"
include "breq12d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "noreson.mm"
include "sltval.mm"
include "mpbird.mm"
include "cxp.mm"
include "cin.mm"
include "df-res.mm"
include "2on.mm"
include "xpsng.mm"
include "sylancl.mm"
include "ineq1d.mm"
include "incom.mm"
include "word.mm"
include "nodmord.mm"
include "ordirr.mm"
include "3syl.mm"
include "disjsn.mm"
include "syl5eq.mm"
include "xpdisj1.mm"
include "eqtr3d.mm"
include "uneq2d.mm"
include "resundir.mm"
include "un0.mm"
include "eqcomi.mm"
include "3eqtr4g.mm"
include "wfun.mm"
include "wrel.mm"
include "nofun.mm"
include "funrel.mm"
include "resdm.mm"
include "eqtrd.mm"
include "sssucid.mm"
include "resabs1.mm"
include "mp1i.mm"
include "3brtr4d.mm"
include "elexi.mm"
include "prid2.mm"
include "noextend.mm"
include "sucelon.mm"
include "sylib.mm"
include "sltres.mm"
include "mpd.mm"
include "soasym.mm"
include "df-suc.mm"
include "reseq2i.mm"
include "resundi.mm"
include "eqtri.mm"
include "dmres.mm"
include "necom.mm"
include "rabbii.mm"
include "inteqi.mm"
include "necomd.mm"
include "syl5eqss.mm"
include "eqsstr3d.mm"
include "df-ss.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "nesym.mm"
include "ex.mm"
include "sylbid.mm"
include "ralrimiv.mm"
include "funres.mm"
include "eqfunfv.mm"
include "mpbir2and.mm"
include "wfn.mm"
include "funfn.mm"
include "1on.mm"
include "prid1.mm"
include "nosgnn0i.mm"
include "ndmfv.mm"
include "neeq1d.mm"
include "mpbiri.mm"
include "neneqd.mm"
include "intnanrd.mm"
include "w3o.mm"
include "adantl.mm"
include "3brtr3d.mm"
include "fvex.mm"
include "brtp.mm"
include "3orrot.mm"
include "3bitri.mm"
include "ecase23d.mm"
include "simprd.mm"
include "neeq1.mm"
include "con4i.mm"
include "fnressn.mm"
include "opeq2d.mm"
include "sneqd.mm"
include "uneq12d.mm"
include "eqnbrtrd.mm"
include "jaodan.mm"
include "mpdan.mm"

theorem nosupbnd2lem1
  let vy: setvar y
  let cA: class A
  let cU: class U
  let cZ: class Z
  let va: setvar a
  let vq: setvar q
  let vp: setvar p
  let vx: setvar x

  disjoint A a
  disjoint U a
  disjoint Z a
  disjoint a q
  disjoint A q
  disjoint p q
  disjoint p x
  disjoint q x
  disjoint q y
  disjoint U p
  disjoint U q
  disjoint U x
  disjoint Z p
  disjoint Z q
  disjoint Z x
  assert |- ( ( ( U e. A /\ A. y e. A -. U <s y ) /\ ( A C_ No /\ A e. _V /\ Z e. No ) /\ A. a e. A a <s Z ) -> -. ( Z |` suc dom U ) <s ( U u. { <. dom U , 2o >. } ) )

  proof
    cU
    cA
    wcel
    #
    cU
    vy
    cv
    cslt
    wbr
    wn
    vy
    cA
    wral
    #
    wa
    #
    cA
    csur
    wss
    #
    cA
    cvv
    wcel
    #
    cZ
    csur
    wcel
    #
    w3a
    #
    va
    cv
    #
    cZ
    cslt
    wbr
    #
    va
    cA
    wral
    #
    w3a
    #
    cU
    cZ
    cslt
    wbr
    #
    cZ
    cU
    cdm
    #
    csuc
    #
    cres
    #
    cU
    @12
    c2o
    cop
    #
    csn
    #
    cun
    #
    cslt
    wbr
    wn
    #
    @10
    @0
    @9
    @11
    @0
    @1
    @6
    @9
    simp1l
    #
    @2
    @6
    @9
    simp3
    @8
    @11
    va
    cU
    cA
    @7
    cU
    cZ
    cslt
    breq1
    rspcv
    sylc
    @10
    @11
    wa
    #
    vx
    cv
    #
    cU
    cfv
    #
    @21
    cZ
    cfv
    #
    wne
    #
    vx
    con0
    crab
    #
    cint
    #
    @12
    wss
    #
    @18
    @20
    cU
    csur
    wcel
    #
    @5
    cU
    cZ
    wne
    #
    @27
    @20
    cA
    csur
    cU
    @3
    @4
    @5
    @2
    @9
    @11
    simpl21
    @0
    @1
    @6
    @9
    @11
    simpl1l
    sseldd
    #
    @3
    @4
    @5
    @2
    @9
    @11
    simpl23
    #
    @20
    cU
    cZ
    @10
    @11
    cU
    cZ
    wceq
    #
    wn
    @10
    @32
    @11
    @10
    cU
    cU
    cslt
    wbr
    #
    wn
    #
    @32
    @11
    wn
    @10
    @28
    @34
    @10
    cA
    csur
    cU
    @2
    @3
    @4
    @5
    @9
    simp21
    @19
    sseldd
    csur
    cslt
    wor
    #
    @28
    @34
    sltso
    csur
    cU
    cslt
    sonr
    mpan
    syl
    @32
    @33
    @11
    cU
    cZ
    cU
    cslt
    breq2
    notbid
    syl5ibcom
    con2d
    imp
    neqned
    #
    vx
    cU
    cZ
    nosepssdm
    syl3anc
    @20
    @27
    @26
    @12
    wcel
    #
    @26
    @12
    wceq
    #
    wo
    #
    @18
    @20
    @26
    con0
    wcel
    #
    @12
    con0
    wcel
    #
    @27
    @39
    wb
    @20
    @28
    @5
    @29
    @40
    @30
    @31
    @36
    vx
    cU
    cZ
    nosepon
    #
    syl3anc
    @20
    @28
    @41
    @30
    cU
    nodmon
    #
    syl
    #
    @26
    @12
    onsseleq
    syl2anc
    @20
    @39
    @18
    @20
    @37
    @18
    @38
    @20
    @37
    wa
    #
    @17
    @14
    cslt
    wbr
    #
    @18
    @45
    @17
    @12
    cres
    #
    @14
    @12
    cres
    #
    cslt
    wbr
    #
    @46
    @45
    cU
    cZ
    @12
    cres
    #
    @47
    @48
    cslt
    @45
    cU
    @50
    cslt
    wbr
    #
    vq
    cv
    #
    cU
    cfv
    #
    @52
    @50
    cfv
    #
    wceq
    #
    vq
    vp
    cv
    #
    wral
    #
    @56
    cU
    cfv
    #
    @56
    @50
    cfv
    #
    c1o
    c0
    cop
    c1o
    c2o
    cop
    c0
    c2o
    cop
    ctp
    #
    wbr
    #
    wa
    #
    vp
    con0
    wrex
    #
    @45
    @40
    @55
    vq
    @26
    wral
    #
    @26
    cU
    cfv
    #
    @26
    @50
    cfv
    #
    @60
    wbr
    #
    @63
    @45
    @28
    @5
    @29
    @40
    @20
    @28
    @37
    @30
    adantr
    #
    @20
    @5
    @37
    @31
    adantr
    #
    @20
    @29
    @37
    @36
    adantr
    @42
    syl3anc
    #
    @45
    @55
    vq
    @26
    @45
    @52
    @26
    wcel
    #
    wa
    #
    @53
    @52
    cZ
    cfv
    #
    @54
    @72
    @53
    @73
    wne
    #
    wn
    #
    @53
    @73
    wceq
    #
    @72
    @52
    con0
    wcel
    #
    @71
    @75
    @45
    @40
    @71
    @77
    @70
    @26
    @52
    onelon
    sylan
    @45
    @71
    simpr
    #
    @24
    @74
    vx
    @52
    vx
    vq
    weq
    @22
    @53
    @23
    @73
    @21
    @52
    cU
    fveq2
    @21
    @52
    cZ
    fveq2
    neeq12d
    onnminsb
    #
    sylc
    @74
    @76
    @53
    @73
    df-ne
    con2bii
    sylibr
    @72
    @52
    @12
    cZ
    @72
    @71
    @37
    @52
    @12
    wcel
    #
    @78
    @20
    @37
    @71
    simplr
    @72
    @41
    @71
    @37
    wa
    @80
    wi
    @45
    @41
    @71
    @20
    @41
    @37
    @44
    adantr
    #
    adantr
    @52
    @26
    @12
    ontr1
    syl
    mp2and
    fvresd
    eqtr4d
    ralrimiva
    @45
    @65
    @26
    cZ
    cfv
    #
    @66
    @60
    @45
    @11
    @65
    @82
    @60
    wbr
    #
    @10
    @11
    @37
    simplr
    @45
    @28
    @5
    @11
    @83
    wb
    #
    @68
    @69
    cU
    cZ
    vx
    sltval2
    #
    syl2anc
    mpbid
    @45
    @26
    @12
    cZ
    @20
    @37
    simpr
    fvresd
    breqtrrd
    @62
    @64
    @67
    wa
    vp
    @26
    con0
    @56
    @26
    wceq
    #
    @57
    @64
    @61
    @67
    @55
    vq
    @56
    @26
    raleq
    @86
    @58
    @65
    @59
    @66
    @60
    @56
    @26
    cU
    fveq2
    @56
    @26
    @50
    fveq2
    breq12d
    anbi12d
    rspcev
    syl12anc
    @45
    @28
    @50
    csur
    wcel
    #
    @51
    @63
    wb
    @68
    @45
    @5
    @41
    @87
    @69
    @81
    cZ
    @12
    noreson
    syl2anc
    vp
    vq
    cU
    @50
    sltval
    syl2anc
    mpbird
    @45
    @47
    cU
    @12
    cres
    #
    cU
    @45
    @88
    @16
    @12
    cres
    #
    cun
    @88
    c0
    cun
    #
    @47
    @88
    @45
    @89
    c0
    @88
    @45
    @89
    @16
    @12
    cvv
    cxp
    #
    cin
    #
    c0
    @16
    @12
    df-res
    @45
    @12
    csn
    #
    c2o
    csn
    #
    cxp
    #
    @91
    cin
    #
    @92
    c0
    @45
    @95
    @16
    @91
    @45
    @41
    c2o
    con0
    wcel
    @95
    @16
    wceq
    @81
    2on
    @12
    c2o
    con0
    con0
    xpsng
    sylancl
    ineq1d
    @45
    @93
    @12
    cin
    #
    c0
    wceq
    @96
    c0
    wceq
    @45
    @97
    @12
    @93
    cin
    #
    c0
    @93
    @12
    incom
    @45
    @12
    @12
    wcel
    wn
    #
    @98
    c0
    wceq
    @45
    @28
    @12
    word
    #
    @99
    @68
    cU
    nodmord
    #
    @12
    ordirr
    #
    3syl
    @12
    @12
    disjsn
    sylibr
    syl5eq
    @93
    @12
    @94
    cvv
    xpdisj1
    syl
    eqtr3d
    syl5eq
    uneq2d
    cU
    @16
    @12
    resundir
    @90
    @88
    @88
    un0
    eqcomi
    3eqtr4g
    @45
    cU
    wfun
    #
    cU
    wrel
    @88
    cU
    wceq
    @45
    @28
    @103
    @68
    cU
    nofun
    #
    syl
    cU
    funrel
    cU
    resdm
    3syl
    eqtrd
    @12
    @13
    wss
    @48
    @50
    wceq
    @45
    @12
    sssucid
    cZ
    @12
    @13
    resabs1
    mp1i
    3brtr4d
    @45
    @17
    csur
    wcel
    #
    @14
    csur
    wcel
    #
    @41
    @49
    @46
    wi
    @20
    @105
    @37
    @20
    @28
    @105
    @30
    cU
    c2o
    c1o
    c2o
    c2o
    con0
    2on
    elexi
    prid2
    #
    noextend
    #
    syl
    adantr
    #
    @20
    @106
    @37
    @20
    @5
    @13
    con0
    wcel
    #
    @106
    @31
    @20
    @41
    @110
    @44
    @12
    sucelon
    sylib
    cZ
    @13
    noreson
    syl2anc
    adantr
    #
    @81
    @17
    @14
    @12
    sltres
    syl3anc
    mpd
    @45
    @105
    @106
    @46
    @18
    wi
    #
    @109
    @111
    @35
    @105
    @106
    wa
    @112
    sltso
    csur
    cslt
    @17
    @14
    soasym
    mpan
    syl2anc
    mpd
    @20
    @38
    wa
    #
    @14
    @17
    @17
    cslt
    @113
    @14
    @50
    cZ
    @93
    cres
    #
    cun
    #
    @17
    @14
    cZ
    @12
    @93
    cun
    #
    cres
    @115
    @13
    @116
    cZ
    @12
    df-suc
    reseq2i
    cZ
    @12
    @93
    resundi
    eqtri
    @113
    @50
    cU
    @114
    @16
    @113
    @50
    cU
    wceq
    #
    @50
    cdm
    #
    @12
    wceq
    #
    @54
    @53
    wceq
    #
    vq
    @118
    wral
    #
    @113
    @118
    @12
    cZ
    cdm
    #
    cin
    #
    @12
    cZ
    @12
    dmres
    @113
    @12
    @122
    wss
    @123
    @12
    wceq
    @113
    @12
    @26
    @122
    @20
    @38
    simpr
    #
    @113
    @26
    @23
    @22
    wne
    #
    vx
    con0
    crab
    #
    cint
    #
    @122
    @25
    @126
    @24
    @125
    vx
    con0
    @22
    @23
    necom
    rabbii
    inteqi
    @113
    @5
    @28
    cZ
    cU
    wne
    @127
    @122
    wss
    @20
    @5
    @38
    @31
    adantr
    #
    @20
    @28
    @38
    @30
    adantr
    #
    @113
    cU
    cZ
    @20
    @29
    @38
    @36
    adantr
    necomd
    vx
    cZ
    cU
    nosepssdm
    syl3anc
    syl5eqss
    eqsstr3d
    @12
    @122
    df-ss
    sylib
    syl5eq
    #
    @113
    @120
    vq
    @118
    @113
    @52
    @118
    wcel
    @80
    @120
    @113
    @118
    @12
    @52
    @130
    eleq2d
    @113
    @80
    @120
    @113
    @80
    wa
    #
    @54
    @73
    @53
    @131
    @52
    @12
    cZ
    @113
    @80
    simpr
    fvresd
    @131
    @75
    @73
    @53
    wceq
    #
    @131
    @77
    @71
    @75
    @113
    @41
    @80
    @77
    @113
    @28
    @41
    @129
    @43
    syl
    @12
    @52
    onelon
    sylan
    @113
    @71
    @80
    @113
    @26
    @12
    @52
    @124
    eleq2d
    biimpar
    @79
    sylc
    @74
    @132
    @53
    @73
    nesym
    con2bii
    sylibr
    eqtrd
    ex
    sylbid
    ralrimiv
    @113
    @50
    wfun
    #
    @103
    @117
    @119
    @121
    wa
    wb
    @113
    @5
    cZ
    wfun
    #
    @133
    @128
    cZ
    nofun
    #
    @12
    cZ
    funres
    3syl
    @113
    @28
    @103
    @129
    @104
    syl
    vq
    @50
    cU
    eqfunfv
    syl2anc
    mpbir2and
    @113
    @114
    @12
    @12
    cZ
    cfv
    #
    cop
    #
    csn
    #
    @16
    @113
    cZ
    @122
    wfn
    #
    @12
    @122
    wcel
    #
    @114
    @138
    wceq
    @113
    @134
    @139
    @113
    @5
    @134
    @128
    @135
    syl
    cZ
    funfn
    sylib
    @113
    @136
    c2o
    wceq
    #
    @140
    @113
    @12
    cU
    cfv
    #
    c0
    wceq
    #
    @141
    @113
    @143
    @141
    wa
    #
    @142
    c1o
    wceq
    #
    @136
    c0
    wceq
    #
    wa
    #
    @145
    @141
    wa
    #
    @113
    @145
    @146
    @113
    @142
    c1o
    @113
    @142
    c1o
    wne
    c0
    c1o
    wne
    c1o
    c1o
    c2o
    c1o
    con0
    1on
    elexi
    prid1
    nosgnn0i
    @113
    @142
    c0
    c1o
    @113
    @100
    @99
    @143
    @113
    @28
    @100
    @129
    @101
    syl
    @102
    @12
    cU
    ndmfv
    3syl
    neeq1d
    mpbiri
    neneqd
    #
    intnanrd
    @113
    @145
    @141
    @149
    intnanrd
    @113
    @142
    @136
    @60
    wbr
    #
    @144
    @147
    @148
    w3o
    #
    @113
    @65
    @82
    @142
    @136
    @60
    @113
    @11
    @83
    @10
    @11
    @38
    simplr
    @113
    @28
    @5
    @84
    @129
    @128
    @85
    syl2anc
    mpbid
    @38
    @65
    @142
    wceq
    @20
    @26
    @12
    cU
    fveq2
    adantl
    @38
    @82
    @136
    wceq
    @20
    @26
    @12
    cZ
    fveq2
    adantl
    3brtr3d
    @150
    @147
    @148
    @144
    w3o
    @148
    @144
    @147
    w3o
    @151
    c1o
    c0
    c1o
    c2o
    c0
    c2o
    @142
    @136
    @12
    cU
    fvex
    @12
    cZ
    fvex
    brtp
    @147
    @148
    @144
    3orrot
    @148
    @144
    @147
    3orrot
    3bitri
    sylib
    ecase23d
    simprd
    #
    @140
    @141
    @140
    wn
    @146
    @141
    wn
    @12
    cZ
    ndmfv
    @146
    @136
    c2o
    @146
    @136
    c2o
    wne
    c0
    c2o
    wne
    c2o
    @107
    nosgnn0i
    @136
    c0
    c2o
    neeq1
    mpbiri
    neneqd
    syl
    con4i
    syl
    @122
    @12
    cZ
    fnressn
    syl2anc
    @113
    @137
    @15
    @113
    @136
    c2o
    @12
    @152
    opeq2d
    sneqd
    eqtrd
    uneq12d
    syl5eq
    @113
    @28
    @105
    @17
    @17
    cslt
    wbr
    wn
    #
    @129
    @108
    @35
    @105
    @153
    sltso
    csur
    @17
    cslt
    sonr
    mpan
    3syl
    eqnbrtrd
    jaodan
    ex
    sylbid
    mpd
    mpdan
end
