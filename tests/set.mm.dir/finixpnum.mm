include "cfn.mm"
include "wcel.mm"
include "ccrd.mm"
include "cdm.mm"
include "wral.mm"
include "cixp.mm"
include "cv.mm"
include "wi.mm"
include "c0.mm"
include "csn.mm"
include "csb.mm"
include "wa.mm"
include "cun.mm"
include "wceq.mm"
include "raleq.mm"
include "ixpeq1.mm"
include "ixp0x.mm"
include "syl6eq.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "weq.mm"
include "ralunb.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "wsbc.mm"
include "ralsnsg.mm"
include "sbcel1g.mm"
include "bitrd.mm"
include "ax-mp.mm"
include "anbi2i.mm"
include "bitri.mm"
include "syl6bb.mm"
include "snfi.mm"
include "finnum.mm"
include "mp1i.mm"
include "wel.mm"
include "wn.mm"
include "pm2.27.mm"
include "cxp.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cop.mm"
include "cmpt.mm"
include "wfo.mm"
include "xpnum.mm"
include "ancoms.mm"
include "wf.mm"
include "wrex.mm"
include "wfn.mm"
include "cin.mm"
include "xp1st.mm"
include "ixpfn.mm"
include "syl.mm"
include "fvex.mm"
include "fnsn.mm"
include "jctir.mm"
include "disjsn.mm"
include "biimpri.mm"
include "fnun.mm"
include "syl2anr.mm"
include "elixp.mm"
include "sylib.mm"
include "fvun1.mm"
include "mp3an2.mm"
include "anassrs.mm"
include "biimprd.mm"
include "ralimdva.mm"
include "impr.mm"
include "syl2an.mm"
include "vsnid.mm"
include "fvun2.mm"
include "csbfv.mm"
include "fvsn.mm"
include "eqcomi.mm"
include "3eqtr4g.mm"
include "xp2nd.mm"
include "adantl.mm"
include "eqeltrd.mm"
include "sbcel12.mm"
include "sylibr.mm"
include "ralun.mm"
include "syl2anc.mm"
include "snex.mm"
include "unex.mm"
include "sylanbrc.mm"
include "eqid.mm"
include "fmptd.mm"
include "cres.mm"
include "wss.mm"
include "ssun1.mm"
include "fnssres.mm"
include "sylancl.mm"
include "ssralv.mm"
include "fvres.mm"
include "ralimia.mm"
include "sylbi.mm"
include "resex.mm"
include "ssun2.mm"
include "sselii.mm"
include "csbeq1.mm"
include "fvixp.mm"
include "mpan2.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbvixp.mm"
include "eleq2s.mm"
include "opelxpi.mm"
include "cdif.mm"
include "disj3.mm"
include "sylbb1.mm"
include "difun2.mm"
include "syl6eqr.mm"
include "reseq2d.mm"
include "uneq1d.mm"
include "adantr.mm"
include "op1std.mm"
include "op2ndd.mm"
include "opeq2d.mm"
include "sneqd.mm"
include "uneq12d.mm"
include "fvmpt.mm"
include "fnsnsplit.mm"
include "3eqtr4rd.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "ralrimiva.mm"
include "dffo3.mm"
include "fonum.mm"
include "expr.mm"
include "syl9r.mm"
include "expimpd.mm"
include "ancomsd.mm"
include "com23.mm"
include "findcard2s.mm"
include "imp.mm"

theorem finixpnum
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint B y
  disjoint B z
  assert |- ( ( A e. Fin /\ A. x e. A B e. dom card ) -> X_ x e. A B e. dom card )

  proof
    cA
    cfn
    wcel
    cB
    ccrd
    cdm
    #
    wcel
    #
    vx
    cA
    wral
    #
    vx
    cA
    cB
    cixp
    #
    @0
    wcel
    #
    @1
    vx
    vw
    cv
    #
    wral
    #
    vx
    @5
    cB
    cixp
    #
    @0
    wcel
    #
    wi
    @1
    vx
    c0
    wral
    #
    c0
    csn
    #
    @0
    wcel
    #
    wi
    @1
    vx
    vy
    cv
    #
    wral
    #
    vx
    @12
    cB
    cixp
    #
    @0
    wcel
    #
    wi
    #
    @13
    vx
    vz
    cv
    #
    cB
    csb
    #
    @0
    wcel
    #
    wa
    #
    vx
    @12
    @17
    csn
    #
    cun
    #
    cB
    cixp
    #
    @0
    wcel
    #
    wi
    #
    @2
    @4
    wi
    vw
    vy
    vz
    cA
    @5
    c0
    wceq
    #
    @6
    @9
    @8
    @11
    @1
    vx
    @5
    c0
    raleq
    @26
    @7
    @10
    @0
    @26
    @7
    vx
    c0
    cB
    cixp
    @10
    vx
    @5
    c0
    cB
    ixpeq1
    vx
    cB
    ixp0x
    syl6eq
    eleq1d
    imbi12d
    vw
    vy
    weq
    #
    @6
    @13
    @8
    @15
    @1
    vx
    @5
    @12
    raleq
    @27
    @7
    @14
    @0
    vx
    @5
    @12
    cB
    ixpeq1
    eleq1d
    imbi12d
    @5
    @22
    wceq
    #
    @6
    @20
    @8
    @24
    @28
    @6
    @1
    vx
    @22
    wral
    #
    @20
    @1
    vx
    @5
    @22
    raleq
    @29
    @13
    @1
    vx
    @21
    wral
    #
    wa
    @20
    @1
    vx
    @12
    @21
    ralunb
    @30
    @19
    @13
    @17
    cvv
    wcel
    #
    @30
    @19
    wb
    vz
    vex
    #
    @31
    @30
    @1
    vx
    @17
    wsbc
    @19
    @1
    vx
    @17
    cvv
    ralsnsg
    vx
    @17
    cB
    @0
    cvv
    sbcel1g
    bitrd
    ax-mp
    anbi2i
    bitri
    syl6bb
    @28
    @7
    @23
    @0
    vx
    @5
    @22
    cB
    ixpeq1
    eleq1d
    imbi12d
    @5
    cA
    wceq
    #
    @6
    @2
    @8
    @4
    @1
    vx
    @5
    cA
    raleq
    @33
    @7
    @3
    @0
    vx
    @5
    cA
    cB
    ixpeq1
    eleq1d
    imbi12d
    @10
    cfn
    wcel
    @11
    @9
    c0
    snfi
    @10
    finnum
    mp1i
    vz
    vy
    wel
    wn
    #
    @16
    @25
    wi
    @12
    cfn
    wcel
    @34
    @20
    @16
    @24
    @34
    @19
    @13
    @16
    @24
    wi
    #
    @34
    @19
    @13
    @35
    @13
    @16
    @15
    @34
    @19
    wa
    @24
    @13
    @15
    pm2.27
    @34
    @19
    @15
    @24
    @19
    @15
    wa
    @14
    @18
    cxp
    #
    @0
    wcel
    #
    @36
    @23
    vw
    @36
    @5
    c1st
    cfv
    #
    @17
    @5
    c2nd
    cfv
    #
    cop
    #
    csn
    #
    cun
    #
    cmpt
    #
    wfo
    #
    @24
    @34
    @15
    @19
    @37
    @14
    @18
    xpnum
    ancoms
    @34
    @36
    @23
    @43
    wf
    vu
    cv
    #
    vv
    cv
    #
    @43
    cfv
    #
    wceq
    #
    vv
    @36
    wrex
    #
    vu
    @23
    wral
    @44
    @34
    vw
    @36
    @42
    @23
    @43
    @34
    @5
    @36
    wcel
    #
    wa
    #
    @42
    @22
    wfn
    #
    vx
    cv
    #
    @42
    cfv
    #
    cB
    wcel
    #
    vx
    @22
    wral
    #
    @42
    @23
    wcel
    @50
    @38
    @12
    wfn
    #
    @41
    @21
    wfn
    #
    wa
    @12
    @21
    cin
    c0
    wceq
    #
    @52
    @34
    @50
    @57
    @58
    @50
    @38
    @14
    wcel
    #
    @57
    @5
    @14
    @18
    xp1st
    #
    vx
    @12
    cB
    @38
    ixpfn
    syl
    #
    @17
    @39
    @32
    @5
    c2nd
    fvex
    #
    fnsn
    #
    jctir
    @59
    @34
    @12
    @17
    disjsn
    #
    biimpri
    #
    @12
    @21
    @38
    @41
    fnun
    syl2anr
    @51
    @55
    vx
    @12
    wral
    #
    @55
    vx
    @21
    wral
    #
    @56
    @34
    @59
    @57
    @53
    @38
    cfv
    #
    cB
    wcel
    #
    vx
    @12
    wral
    #
    wa
    #
    @67
    @50
    @66
    @50
    @60
    @72
    @61
    vx
    @12
    cB
    @38
    @5
    c1st
    fvex
    #
    elixp
    sylib
    @59
    @57
    @71
    @67
    @57
    @59
    @71
    @67
    wi
    @57
    @59
    wa
    #
    @70
    @55
    vx
    @12
    @74
    vx
    vy
    wel
    #
    wa
    #
    @55
    @70
    @76
    @54
    @69
    cB
    @57
    @59
    @75
    @54
    @69
    wceq
    #
    @57
    @58
    @59
    @75
    wa
    @77
    @64
    @12
    @21
    @38
    @41
    @53
    fvun1
    mp3an2
    anassrs
    eleq1d
    biimprd
    ralimdva
    ancoms
    impr
    syl2an
    @51
    vx
    @17
    @54
    csb
    #
    @18
    wcel
    #
    @68
    @51
    @78
    @39
    @18
    @51
    @17
    @42
    cfv
    #
    @17
    @41
    cfv
    #
    @78
    @39
    @50
    @57
    @59
    @17
    @21
    wcel
    #
    wa
    #
    @80
    @81
    wceq
    #
    @34
    @62
    @34
    @59
    @82
    @66
    vz
    vsnid
    #
    jctir
    @57
    @58
    @83
    @84
    @64
    @12
    @21
    @38
    @41
    @17
    fvun2
    mp3an2
    syl2anr
    vx
    @17
    @42
    csbfv
    @81
    @39
    @17
    @39
    @32
    @63
    fvsn
    eqcomi
    3eqtr4g
    @50
    @39
    @18
    wcel
    @34
    @5
    @14
    @18
    xp2nd
    adantl
    eqeltrd
    @68
    @55
    vx
    @17
    wsbc
    #
    @79
    @31
    @68
    @86
    wb
    @32
    @55
    vx
    @17
    cvv
    ralsnsg
    ax-mp
    vx
    @17
    @54
    cB
    sbcel12
    bitri
    sylibr
    @55
    vx
    @12
    @21
    ralun
    syl2anc
    vx
    @22
    cB
    @42
    @38
    @41
    @73
    @40
    snex
    unex
    elixp
    sylanbrc
    @43
    eqid
    #
    fmptd
    @34
    @49
    vu
    @23
    @34
    @45
    @23
    wcel
    #
    wa
    #
    @45
    @12
    cres
    #
    @17
    @45
    cfv
    #
    cop
    #
    @36
    wcel
    #
    @45
    @92
    @43
    cfv
    #
    wceq
    #
    @49
    @88
    @93
    @34
    @88
    @90
    @14
    wcel
    #
    @91
    @18
    wcel
    #
    @93
    @88
    @90
    @12
    wfn
    #
    @53
    @90
    cfv
    #
    cB
    wcel
    #
    vx
    @12
    wral
    #
    @96
    @88
    @45
    @22
    wfn
    #
    @12
    @22
    wss
    #
    @98
    vx
    @22
    cB
    @45
    ixpfn
    #
    @12
    @21
    ssun1
    #
    @22
    @12
    @45
    fnssres
    sylancl
    @88
    @102
    @53
    @45
    cfv
    #
    cB
    wcel
    #
    vx
    @22
    wral
    #
    wa
    @101
    vx
    @22
    cB
    @45
    vu
    vex
    #
    elixp
    @108
    @101
    @102
    @108
    @107
    vx
    @12
    wral
    #
    @101
    @103
    @108
    @110
    wi
    @105
    @107
    vx
    @12
    @22
    ssralv
    ax-mp
    @107
    @100
    vx
    @12
    @75
    @100
    @107
    @75
    @99
    @106
    cB
    @53
    @12
    @45
    fvres
    eleq1d
    biimprd
    ralimia
    syl
    adantl
    sylbi
    vx
    @12
    cB
    @90
    @45
    @12
    @109
    resex
    #
    elixp
    sylanbrc
    @97
    @45
    vw
    @22
    vx
    @5
    cB
    csb
    #
    cixp
    #
    @23
    @45
    @113
    wcel
    @17
    @22
    wcel
    #
    @97
    @21
    @22
    @17
    @21
    @12
    ssun2
    @85
    sselii
    #
    vw
    @22
    @112
    @17
    @18
    @45
    vx
    @5
    @17
    cB
    csbeq1
    fvixp
    mpan2
    vx
    vw
    @22
    cB
    @112
    vw
    cB
    nfcv
    vx
    @5
    cB
    nfcsb1v
    vx
    @5
    cB
    csbeq1a
    cbvixp
    eleq2s
    @90
    @91
    @14
    @18
    opelxpi
    syl2anc
    #
    adantl
    @89
    @90
    @17
    @91
    cop
    #
    csn
    #
    cun
    #
    @45
    @22
    @21
    cdif
    #
    cres
    #
    @118
    cun
    #
    @94
    @45
    @34
    @119
    @122
    wceq
    @88
    @34
    @90
    @121
    @118
    @34
    @12
    @120
    @45
    @34
    @12
    @12
    @21
    cdif
    #
    @120
    @59
    @34
    @12
    @123
    wceq
    @65
    @12
    @21
    disj3
    sylbb1
    @12
    @21
    difun2
    syl6eqr
    reseq2d
    uneq1d
    adantr
    @88
    @94
    @119
    wceq
    #
    @34
    @88
    @93
    @124
    @116
    vw
    @92
    @42
    @119
    @36
    @43
    @5
    @92
    wceq
    #
    @38
    @90
    @41
    @118
    @90
    @91
    @5
    @111
    @17
    @45
    fvex
    #
    op1std
    @125
    @40
    @117
    @125
    @39
    @91
    @17
    @90
    @91
    @5
    @111
    @126
    op2ndd
    opeq2d
    sneqd
    uneq12d
    @87
    @90
    @118
    @111
    @117
    snex
    unex
    fvmpt
    syl
    adantl
    @88
    @45
    @122
    wceq
    #
    @34
    @88
    @102
    @114
    @127
    @104
    @115
    @22
    @45
    @17
    fnsnsplit
    sylancl
    adantl
    3eqtr4rd
    @48
    @95
    vv
    @92
    @36
    @46
    @92
    wceq
    @47
    @94
    @45
    @46
    @92
    @43
    fveq2
    eqeq2d
    rspcev
    syl2anc
    ralrimiva
    vv
    vu
    @36
    @23
    @43
    dffo3
    sylanbrc
    @36
    @23
    @43
    fonum
    syl2anr
    expr
    syl9r
    expimpd
    ancomsd
    com23
    adantl
    findcard2s
    imp
end
