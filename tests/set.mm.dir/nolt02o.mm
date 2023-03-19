include "csur.mm"
include "wcel.mm"
include "con0.mm"
include "w3a.mm"
include "cres.mm"
include "wceq.mm"
include "cslt.mm"
include "wbr.mm"
include "wa.mm"
include "cfv.mm"
include "c0.mm"
include "c2o.mm"
include "c1o.mm"
include "wn.mm"
include "simp11.mm"
include "wor.mm"
include "sltso.mm"
include "sonr.mm"
include "mpan.mm"
include "syl.mm"
include "simp2r.mm"
include "breq2.mm"
include "syl5ibrcom.mm"
include "mtod.mm"
include "simpl2l.mm"
include "wrel.mm"
include "cdm.mm"
include "wss.mm"
include "wfun.mm"
include "simpl11.mm"
include "nofun.mm"
include "funrel.mm"
include "3syl.mm"
include "simpl13.mm"
include "simpl3.mm"
include "nolt02olem.mm"
include "syl3anc.mm"
include "relssres.mm"
include "syl2anc.mm"
include "simpl12.mm"
include "simpr.mm"
include "3eqtr3d.mm"
include "mtand.mm"
include "cv.mm"
include "wral.mm"
include "cop.mm"
include "ctp.mm"
include "wi.mm"
include "wrex.mm"
include "wb.mm"
include "simp12.mm"
include "sltval.mm"
include "mpbid.mm"
include "df-an.mm"
include "rexbii.mm"
include "rexnal.mm"
include "bitri.mm"
include "sylib.mm"
include "1on.mm"
include "elexi.mm"
include "prid1.mm"
include "nosgnn0i.mm"
include "neii.mm"
include "simpll3.mm"
include "simplr.mm"
include "eqeq1.mm"
include "anbi1d.mm"
include "eqtr2.mm"
include "syl6bi.mm"
include "com12.mm"
include "mtoi.mm"
include "simplrr.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "simprl.mm"
include "adantr.mm"
include "ontri1.mm"
include "mpbird.mm"
include "wo.mm"
include "onsseleq.mm"
include "ancoms.mm"
include "mto.mm"
include "csuc.mm"
include "df-1o.mm"
include "df-2o.mm"
include "eqeq12i.mm"
include "0elon.mm"
include "suc11.mm"
include "mp2an.mm"
include "nemtbir.mm"
include "2on.mm"
include "prid2.mm"
include "3pm3.2i.mm"
include "w3o.mm"
include "fvex.mm"
include "brtp.mm"
include "3oran.mm"
include "con2bii.mm"
include "mpbi.mm"
include "fveq1d.mm"
include "breq2d.mm"
include "mtbii.mm"
include "fvres.mm"
include "breq12d.mm"
include "notbid.mm"
include "syl5ibcom.mm"
include "intnanr.mm"
include "intnan.mm"
include "0ex.mm"
include "mtbiri.mm"
include "jaod.mm"
include "sylbid.mm"
include "mpd.mm"
include "expr.mm"
include "ralrimiva.mm"
include "nofv.mm"
include "3orrot.mm"
include "ecase23d.mm"

theorem nolt02o
  let cA: class A
  let cB: class B
  let cX: class X
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( ( A e. No /\ B e. No /\ X e. On ) /\ ( ( A |` X ) = ( B |` X ) /\ A <s B ) /\ ( A ` X ) = (/) ) -> ( B ` X ) = 2o )

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
    wceq
    #
    cA
    cB
    cslt
    wbr
    #
    wa
    #
    cX
    cA
    cfv
    #
    c0
    wceq
    #
    w3a
    #
    cX
    cB
    cfv
    #
    c2o
    wceq
    #
    @12
    c0
    wceq
    #
    @12
    c1o
    wceq
    #
    @11
    @14
    cA
    cB
    wceq
    #
    @11
    @16
    cA
    cA
    cslt
    wbr
    #
    @11
    @0
    @17
    wn
    #
    @0
    @1
    @2
    @8
    @10
    simp11
    #
    csur
    cslt
    wor
    @0
    @18
    sltso
    csur
    cA
    cslt
    sonr
    mpan
    syl
    @11
    @17
    @16
    @7
    @3
    @6
    @7
    @10
    simp2r
    #
    cA
    cB
    cA
    cslt
    breq2
    syl5ibrcom
    mtod
    @11
    @14
    wa
    #
    @4
    @5
    cA
    cB
    @6
    @7
    @3
    @10
    @14
    simpl2l
    @21
    cA
    wrel
    #
    cA
    cdm
    cX
    wss
    #
    @4
    cA
    wceq
    @21
    @0
    cA
    wfun
    @22
    @0
    @1
    @2
    @8
    @10
    @14
    simpl11
    #
    cA
    nofun
    cA
    funrel
    3syl
    @21
    @0
    @2
    @10
    @23
    @24
    @0
    @1
    @2
    @8
    @10
    @14
    simpl13
    #
    @3
    @8
    @10
    @14
    simpl3
    cA
    cX
    nolt02olem
    syl3anc
    cA
    cX
    relssres
    syl2anc
    @21
    cB
    wrel
    #
    cB
    cdm
    cX
    wss
    #
    @5
    cB
    wceq
    @21
    @1
    cB
    wfun
    @26
    @0
    @1
    @2
    @8
    @10
    @14
    simpl12
    #
    cB
    nofun
    cB
    funrel
    3syl
    @21
    @1
    @2
    @14
    @27
    @28
    @25
    @11
    @14
    simpr
    cB
    cX
    nolt02olem
    syl3anc
    cB
    cX
    relssres
    syl2anc
    3eqtr3d
    mtand
    @11
    @15
    vy
    cv
    #
    cA
    cfv
    #
    @29
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
    @33
    cA
    cfv
    #
    @33
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
    wn
    #
    wi
    #
    vx
    con0
    wral
    #
    @11
    @34
    @38
    wa
    #
    vx
    con0
    wrex
    #
    @41
    wn
    #
    @11
    @7
    @43
    @20
    @11
    @0
    @1
    @7
    @43
    wb
    @19
    @0
    @1
    @2
    @8
    @10
    simp12
    #
    vx
    vy
    cA
    cB
    sltval
    syl2anc
    mpbid
    @43
    @40
    wn
    #
    vx
    con0
    wrex
    @44
    @42
    @46
    vx
    con0
    @34
    @38
    df-an
    rexbii
    @40
    vx
    con0
    rexnal
    bitri
    sylib
    @11
    @15
    wa
    #
    @40
    vx
    con0
    @47
    @33
    con0
    wcel
    #
    @34
    @39
    @47
    @48
    @34
    wa
    #
    wa
    #
    @33
    cX
    wss
    #
    @39
    @50
    @51
    cX
    @33
    wcel
    #
    wn
    #
    @50
    @52
    @9
    @12
    wceq
    #
    @50
    @54
    c0
    c1o
    wceq
    #
    c0
    c1o
    c1o
    c1o
    c2o
    c1o
    con0
    1on
    elexi
    #
    prid1
    nosgnn0i
    #
    neii
    #
    @50
    @10
    @15
    @54
    @55
    wi
    @3
    @8
    @10
    @15
    @49
    simpll3
    #
    @11
    @15
    @49
    simplr
    #
    @54
    @10
    @15
    wa
    #
    @55
    @54
    @61
    @14
    @15
    wa
    @55
    @54
    @10
    @14
    @15
    @9
    @12
    c0
    eqeq1
    anbi1d
    @12
    c0
    c1o
    eqtr2
    syl6bi
    com12
    syl2anc
    mtoi
    @50
    @52
    wa
    @52
    @34
    @54
    @50
    @52
    simpr
    @47
    @48
    @34
    @52
    simplrr
    @32
    @54
    vy
    cX
    @33
    @29
    cX
    wceq
    @30
    @9
    @31
    @12
    @29
    cX
    cA
    fveq2
    @29
    cX
    cB
    fveq2
    eqeq12d
    rspcv
    sylc
    mtand
    @50
    @48
    @2
    @51
    @53
    wb
    @47
    @48
    @34
    simprl
    #
    @47
    @2
    @49
    @0
    @1
    @2
    @8
    @10
    @15
    simpl13
    adantr
    #
    @33
    cX
    ontri1
    syl2anc
    mpbird
    @50
    @51
    @33
    cX
    wcel
    #
    @33
    cX
    wceq
    #
    wo
    #
    @39
    @50
    @48
    @2
    @51
    @66
    wb
    @62
    @63
    @33
    cX
    onsseleq
    syl2anc
    @50
    @64
    @39
    @65
    @50
    @33
    @4
    cfv
    #
    @33
    @5
    cfv
    #
    @37
    wbr
    #
    wn
    @64
    @39
    @50
    @67
    @67
    @37
    wbr
    #
    @69
    @67
    c1o
    wceq
    #
    @67
    c0
    wceq
    #
    wa
    #
    wn
    #
    @71
    @67
    c2o
    wceq
    #
    wa
    #
    wn
    #
    @72
    @75
    wa
    #
    wn
    #
    w3a
    #
    @70
    wn
    @74
    @77
    @79
    @73
    @55
    @58
    @72
    @71
    @55
    @67
    c0
    c1o
    eqtr2
    ancoms
    mto
    @76
    c1o
    c2o
    wceq
    #
    @81
    c0
    c1o
    @57
    @81
    c0
    csuc
    #
    c1o
    csuc
    #
    wceq
    #
    @55
    c1o
    @82
    c2o
    @83
    df-1o
    df-2o
    eqeq12i
    c0
    con0
    wcel
    c1o
    con0
    wcel
    @84
    @55
    wb
    0elon
    1on
    c0
    c1o
    suc11
    mp2an
    bitri
    nemtbir
    #
    @67
    c1o
    c2o
    eqtr2
    mto
    @78
    c0
    c2o
    wceq
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
    @67
    c0
    c2o
    eqtr2
    mto
    3pm3.2i
    @70
    @80
    @70
    @73
    @76
    @78
    w3o
    @80
    wn
    c1o
    c0
    c1o
    c2o
    c0
    c2o
    @67
    @67
    @33
    @4
    fvex
    #
    @86
    brtp
    @73
    @76
    @78
    3oran
    bitri
    con2bii
    mpbi
    @50
    @67
    @68
    @67
    @37
    @50
    @33
    @4
    @5
    @47
    @6
    @49
    @6
    @7
    @3
    @10
    @15
    simpl2l
    adantr
    fveq1d
    breq2d
    mtbii
    @64
    @69
    @38
    @64
    @67
    @35
    @68
    @36
    @37
    @33
    cX
    cA
    fvres
    @33
    cX
    cB
    fvres
    breq12d
    notbid
    syl5ibcom
    @50
    @39
    @65
    @9
    @12
    @37
    wbr
    #
    wn
    @50
    @87
    c0
    c1o
    @37
    wbr
    #
    @55
    c1o
    c0
    wceq
    #
    wa
    #
    wn
    #
    @55
    @81
    wa
    #
    wn
    #
    c0
    c0
    wceq
    #
    @81
    wa
    #
    wn
    #
    w3a
    #
    @88
    wn
    @91
    @93
    @96
    @55
    @89
    @58
    intnanr
    @55
    @81
    @58
    intnanr
    @81
    @94
    @85
    intnan
    3pm3.2i
    @88
    @97
    @88
    @90
    @92
    @95
    w3o
    @97
    wn
    c1o
    c0
    c1o
    c2o
    c0
    c2o
    c0
    c1o
    0ex
    @56
    brtp
    @90
    @92
    @95
    3oran
    bitri
    con2bii
    mpbi
    @50
    @9
    c0
    @12
    c1o
    @37
    @59
    @60
    breq12d
    mtbiri
    @65
    @38
    @87
    @65
    @35
    @9
    @36
    @12
    @37
    @33
    cX
    cA
    fveq2
    @33
    cX
    cB
    fveq2
    breq12d
    notbid
    syl5ibrcom
    jaod
    sylbid
    mpd
    expr
    ralrimiva
    mtand
    @11
    @14
    @15
    @13
    w3o
    #
    @13
    @14
    @15
    w3o
    #
    @11
    @1
    @98
    @45
    cB
    cX
    nofv
    syl
    @98
    @15
    @13
    @14
    w3o
    @99
    @14
    @15
    @13
    3orrot
    @15
    @13
    @14
    3orrot
    bitri
    sylib
    ecase23d
end
