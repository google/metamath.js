include "csur.mm"
include "wcel.mm"
include "con0.mm"
include "w3a.mm"
include "cres.mm"
include "cslt.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "c1o.mm"
include "c0.mm"
include "cop.mm"
include "c2o.mm"
include "ctp.mm"
include "wrex.mm"
include "wne.mm"
include "crab.mm"
include "cint.mm"
include "wi.mm"
include "noreson.mm"
include "3adant2.mm"
include "3adant1.mm"
include "cvv.mm"
include "sltintdifex.mm"
include "onintrab.mm"
include "syl6ib.mm"
include "syl2anc.mm"
include "imp.mm"
include "wss.mm"
include "simpl3.mm"
include "cdm.mm"
include "wo.mm"
include "wb.mm"
include "sltval2.mm"
include "w3o.mm"
include "fvex.mm"
include "brtp.mm"
include "1n0.mm"
include "neii.mm"
include "eqeq1.mm"
include "mtbiri.mm"
include "ndmfv.mm"
include "nsyl2.mm"
include "adantr.mm"
include "orcd.mm"
include "2on.mm"
include "elexi.mm"
include "prid2.mm"
include "nosgnn0i.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "adantl.mm"
include "olcd.mm"
include "3jaoi.mm"
include "sylbi.mm"
include "syl6bi.mm"
include "dmres.mm"
include "elin2.mm"
include "simplbi.mm"
include "jaoi.mm"
include "syl.mm"
include "onelss.mm"
include "sylc.mm"
include "sselda.mm"
include "wn.mm"
include "onelon.mm"
include "sylan.mm"
include "intss1.mm"
include "ontri1.mm"
include "syl5ib.mm"
include "con2d.mm"
include "impancom.mm"
include "mpd.mm"
include "fveq2.mm"
include "neeq12d.mm"
include "elrab.mm"
include "simplbi2.mm"
include "con3d.mm"
include "df-ne.mm"
include "con2bii.mm"
include "sylibr.mm"
include "fvres.mm"
include "eqeq12d.mm"
include "biimpd.mm"
include "ralrimiva.mm"
include "fvresval.mm"
include "ori.mm"
include "eqcomd.mm"
include "eqeq2.mm"
include "mpbid.mm"
include "a1i.mm"
include "ad2antrl.mm"
include "cpr.mm"
include "crn.mm"
include "wfun.mm"
include "nofun.mm"
include "fvelrn.mm"
include "ex.mm"
include "norn.mm"
include "sseld.mm"
include "syld.mm"
include "nosgnn0.mm"
include "eleq1.mm"
include "nsyli.mm"
include "adantrl.mm"
include "jcad.mm"
include "anim12i.mm"
include "ad2antll.mm"
include "adantrr.mm"
include "syl6.mm"
include "3orim123d.mm"
include "3imtr4g.mm"
include "sylbid.mm"
include "raleq.mm"
include "breq12d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "sltval.mm"
include "3adant3.mm"
include "mpbird.mm"

theorem sltres
  let cA: class A
  let cB: class B
  let cX: class X
  let va: setvar a
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. No /\ B e. No /\ X e. On ) -> ( ( A |` X ) <s ( B |` X ) -> A <s B ) )

  proof
    cA
    csur
    wcel
    #
    cB
    csur
    wcel
    #
    cX
    con0
    wcel
    #
    w3a
    #
    cA
    cX
    cres
    #
    cB
    cX
    cres
    #
    cslt
    wbr
    #
    cA
    cB
    cslt
    wbr
    #
    @3
    @6
    wa
    #
    @7
    vy
    cv
    #
    cA
    cfv
    #
    @9
    cB
    cfv
    #
    wceq
    #
    vy
    vx
    cv
    #
    wral
    #
    @13
    cA
    cfv
    #
    @13
    cB
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
    vx
    con0
    wrex
    #
    @8
    va
    cv
    #
    @4
    cfv
    #
    @21
    @5
    cfv
    #
    wne
    #
    va
    con0
    crab
    #
    cint
    #
    con0
    wcel
    #
    @12
    vy
    @26
    wral
    #
    @26
    cA
    cfv
    #
    @26
    cB
    cfv
    #
    @17
    wbr
    #
    @20
    @3
    @6
    @27
    @3
    @4
    csur
    wcel
    #
    @5
    csur
    wcel
    #
    @6
    @27
    wi
    @0
    @2
    @32
    @1
    cA
    cX
    noreson
    3adant2
    #
    @1
    @2
    @33
    @0
    cB
    cX
    noreson
    3adant1
    #
    @32
    @33
    wa
    @6
    @26
    cvv
    wcel
    @27
    @4
    @5
    va
    sltintdifex
    @24
    va
    onintrab
    syl6ib
    syl2anc
    imp
    #
    @8
    @12
    vy
    @26
    @8
    @9
    @26
    wcel
    #
    wa
    #
    @9
    cX
    wcel
    #
    @9
    @4
    cfv
    #
    @9
    @5
    cfv
    #
    wceq
    #
    @12
    @8
    @26
    cX
    @9
    @8
    @2
    @26
    cX
    wcel
    #
    @26
    cX
    wss
    @0
    @1
    @2
    @6
    simpl3
    @8
    @26
    @4
    cdm
    #
    wcel
    #
    @26
    @5
    cdm
    #
    wcel
    #
    wo
    #
    @43
    @3
    @6
    @48
    @3
    @6
    @26
    @4
    cfv
    #
    @26
    @5
    cfv
    #
    @17
    wbr
    #
    @48
    @3
    @32
    @33
    @6
    @51
    wb
    @34
    @35
    @4
    @5
    va
    sltval2
    syl2anc
    #
    @51
    @49
    c1o
    wceq
    #
    @50
    c0
    wceq
    #
    wa
    #
    @53
    @50
    c2o
    wceq
    #
    wa
    #
    @49
    c0
    wceq
    #
    @56
    wa
    #
    w3o
    #
    @48
    c1o
    c0
    c1o
    c2o
    c0
    c2o
    @49
    @50
    @26
    @4
    fvex
    @26
    @5
    fvex
    brtp
    #
    @55
    @48
    @57
    @59
    @55
    @45
    @47
    @53
    @45
    @54
    @53
    @58
    @45
    @53
    @58
    c1o
    c0
    wceq
    c1o
    c0
    1n0
    neii
    @49
    c1o
    c0
    eqeq1
    mtbiri
    #
    @26
    @4
    ndmfv
    nsyl2
    #
    adantr
    orcd
    @57
    @45
    @47
    @53
    @45
    @56
    @63
    adantr
    orcd
    @59
    @47
    @45
    @56
    @47
    @58
    @56
    @54
    @47
    @56
    @54
    c0
    c2o
    wceq
    #
    c0
    c2o
    c2o
    c1o
    c2o
    c2o
    con0
    2on
    elexi
    prid2
    nosgnn0i
    neii
    @56
    @54
    c2o
    c0
    wceq
    @64
    @50
    c2o
    c0
    eqeq1
    c2o
    c0
    eqcom
    syl6bb
    mtbiri
    #
    @26
    @5
    ndmfv
    nsyl2
    #
    adantl
    olcd
    3jaoi
    sylbi
    syl6bi
    imp
    @45
    @43
    @47
    @45
    @43
    @26
    cA
    cdm
    #
    wcel
    #
    @26
    cX
    @67
    @44
    cA
    cX
    dmres
    elin2
    #
    simplbi
    #
    @47
    @43
    @26
    cB
    cdm
    #
    wcel
    #
    @26
    cX
    @71
    @46
    cB
    cX
    dmres
    elin2
    #
    simplbi
    #
    jaoi
    syl
    cX
    @26
    onelss
    sylc
    sselda
    @38
    @40
    @41
    wne
    #
    wn
    #
    @42
    @38
    @9
    con0
    wcel
    #
    @9
    @25
    wcel
    #
    wn
    #
    @76
    @8
    @27
    @37
    @77
    @36
    @26
    @9
    onelon
    sylan
    #
    @38
    @77
    @79
    @80
    @8
    @77
    @37
    @79
    @8
    @27
    @77
    @37
    @79
    wi
    @36
    @27
    @77
    wa
    #
    @78
    @37
    @78
    @26
    @9
    wss
    @81
    @37
    wn
    @9
    @25
    intss1
    @26
    @9
    ontri1
    syl5ib
    con2d
    sylan
    impancom
    mpd
    @77
    @75
    @78
    @78
    @77
    @75
    @24
    @75
    va
    @9
    con0
    @21
    @9
    wceq
    @22
    @40
    @23
    @41
    @21
    @9
    @4
    fveq2
    @21
    @9
    @5
    fveq2
    neeq12d
    elrab
    simplbi2
    con3d
    sylc
    @75
    @42
    @40
    @41
    df-ne
    con2bii
    sylibr
    @39
    @42
    @12
    @39
    @40
    @10
    @41
    @11
    @9
    cX
    cA
    fvres
    @9
    cX
    cB
    fvres
    eqeq12d
    biimpd
    sylc
    ralrimiva
    @3
    @6
    @31
    @3
    @6
    @51
    @31
    @52
    @3
    @60
    @29
    c1o
    wceq
    #
    @30
    c0
    wceq
    #
    wa
    #
    @82
    @30
    c2o
    wceq
    #
    wa
    #
    @29
    c0
    wceq
    #
    @85
    wa
    #
    w3o
    @51
    @31
    @3
    @55
    @84
    @57
    @86
    @59
    @88
    @3
    @55
    @82
    @83
    @55
    @82
    wi
    @3
    @53
    @82
    @54
    @53
    @29
    @49
    wceq
    @82
    @53
    @49
    @29
    @53
    @58
    @49
    @29
    wceq
    #
    @62
    @89
    @58
    @26
    cX
    cA
    fvresval
    ori
    nsyl2
    eqcomd
    @49
    c1o
    @29
    eqeq2
    mpbid
    #
    adantr
    a1i
    @3
    @55
    @83
    @3
    @55
    wa
    #
    @72
    wn
    #
    @83
    @91
    @43
    @47
    wn
    #
    @92
    @91
    @45
    @43
    @53
    @45
    @3
    @54
    @63
    ad2antrl
    @70
    syl
    @3
    @54
    @93
    @53
    @3
    @54
    @93
    @3
    @33
    @54
    @93
    wi
    @35
    @33
    @47
    @50
    c1o
    c2o
    cpr
    #
    wcel
    #
    @54
    @33
    @47
    @50
    @5
    crn
    #
    wcel
    #
    @95
    @33
    @5
    wfun
    #
    @47
    @97
    wi
    @5
    nofun
    @98
    @47
    @97
    @26
    @5
    fvelrn
    ex
    syl
    @33
    @96
    @94
    @50
    @5
    norn
    sseld
    syld
    @54
    @95
    c0
    @94
    wcel
    #
    nosgnn0
    @50
    c0
    @94
    eleq1
    mtbiri
    nsyli
    syl
    imp
    adantrl
    @43
    @72
    @47
    @47
    @43
    @72
    @73
    simplbi2
    con3d
    sylc
    @26
    cB
    ndmfv
    syl
    ex
    jcad
    @57
    @86
    wi
    @3
    @53
    @82
    @56
    @85
    @90
    @56
    @30
    @50
    wceq
    @85
    @56
    @50
    @30
    @56
    @54
    @50
    @30
    wceq
    #
    @65
    @100
    @54
    @26
    cX
    cB
    fvresval
    ori
    nsyl2
    eqcomd
    @50
    c2o
    @30
    eqeq2
    mpbid
    #
    anim12i
    a1i
    @3
    @59
    @87
    @85
    @3
    @59
    @68
    wn
    #
    @87
    @3
    @59
    @102
    @3
    @59
    wa
    #
    @43
    @45
    wn
    #
    @102
    @103
    @47
    @43
    @56
    @47
    @3
    @58
    @66
    ad2antll
    @74
    syl
    @3
    @58
    @104
    @56
    @3
    @58
    @104
    @3
    @32
    @58
    @104
    wi
    @34
    @32
    @45
    @49
    @94
    wcel
    #
    @58
    @32
    @45
    @49
    @4
    crn
    #
    wcel
    #
    @105
    @32
    @4
    wfun
    #
    @45
    @107
    wi
    @4
    nofun
    @108
    @45
    @107
    @26
    @4
    fvelrn
    ex
    syl
    @32
    @106
    @94
    @49
    @4
    norn
    sseld
    syld
    @58
    @105
    @99
    nosgnn0
    @49
    c0
    @94
    eleq1
    mtbiri
    nsyli
    syl
    imp
    adantrr
    @43
    @68
    @45
    @45
    @43
    @68
    @69
    simplbi2
    con3d
    sylc
    ex
    @26
    cA
    ndmfv
    syl6
    @59
    @85
    wi
    @3
    @56
    @85
    @58
    @101
    adantl
    a1i
    jcad
    3orim123d
    @61
    c1o
    c0
    c1o
    c2o
    c0
    c2o
    @29
    @30
    @26
    cA
    fvex
    @26
    cB
    fvex
    brtp
    3imtr4g
    sylbid
    imp
    @19
    @28
    @31
    wa
    vx
    @26
    con0
    @13
    @26
    wceq
    #
    @14
    @28
    @18
    @31
    @12
    vy
    @13
    @26
    raleq
    @109
    @15
    @29
    @16
    @30
    @17
    @13
    @26
    cA
    fveq2
    @13
    @26
    cB
    fveq2
    breq12d
    anbi12d
    rspcev
    syl12anc
    @3
    @7
    @20
    wb
    #
    @6
    @0
    @1
    @110
    @2
    vx
    vy
    cA
    cB
    sltval
    3adant3
    adantr
    mpbird
    ex
end
