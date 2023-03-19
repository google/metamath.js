include "wcel.mm"
include "cgrp.mm"
include "ctmd.mm"
include "cminusg.mm"
include "cfv.mm"
include "ctopn.mm"
include "ccn.mm"
include "co.mm"
include "ctgp.mm"
include "symggrp.mm"
include "cmnd.mm"
include "ctps.mm"
include "cplusg.mm"
include "ctx.mm"
include "grpmnd.mm"
include "syl.mm"
include "cbs.mm"
include "ctopon.mm"
include "cpw.mm"
include "csn.mm"
include "cxp.mm"
include "cpt.mm"
include "crest.mm"
include "eqid.mm"
include "symgtopn.mm"
include "cmap.mm"
include "wss.mm"
include "distopon.mm"
include "pttoponconst.mm"
include "mpdan.mm"
include "cv.mm"
include "wf1o.mm"
include "elsymgbas.mm"
include "wf.mm"
include "f1of.mm"
include "wb.mm"
include "elmapg.mm"
include "anidms.mm"
include "syl5ibr.mm"
include "sylbid.mm"
include "ssrdv.mm"
include "resttopon.mm"
include "syl2anc.mm"
include "eqeltrrd.mm"
include "istps.mm"
include "sylibr.mm"
include "cxko.mm"
include "ccom.mm"
include "cmpt2.mm"
include "symgplusg.mm"
include "ctop.mm"
include "distop.mm"
include "xkotopon.mm"
include "wceq.mm"
include "cndis.mm"
include "sseqtr4d.mm"
include "ccmp.mm"
include "cnlly.mm"
include "clly.mm"
include "disllycmp.mm"
include "llynlly.mm"
include "xkococn.mm"
include "syl3anc.mm"
include "cnmpt2res.mm"
include "syl5eqel.mm"
include "xkopt.mm"
include "mpancom.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "eleqtrd.mm"
include "crn.mm"
include "cplusf.mm"
include "wfn.mm"
include "vex.mm"
include "coex.mm"
include "fnmpt2i.mm"
include "plusfeq.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "grpplusf.mm"
include "frn.mm"
include "3syl.mm"
include "cnrest2.mm"
include "mpbid.mm"
include "oveq2d.mm"
include "istmd.mm"
include "syl3anbrc.mm"
include "ccnv.mm"
include "cmpt.mm"
include "id.mm"
include "fconst6g.mm"
include "wa.mm"
include "ccnp.mm"
include "wral.mm"
include "biimpa.mm"
include "f1ocnv.mm"
include "ffvelrnda.mm"
include "an32s.mm"
include "fmptd.mm"
include "cima.mm"
include "wrex.mm"
include "wi.mm"
include "adantr.mm"
include "weq.mm"
include "cnveq.mm"
include "fveq1d.mm"
include "fvex.mm"
include "fvmpt.mm"
include "ad2antlr.mm"
include "eleq1d.mm"
include "crab.mm"
include "cvv.mm"
include "mptiniseg.mm"
include "ad2antrr.mm"
include "cuni.mm"
include "toponuni.mm"
include "mpteq1.mm"
include "simpll.mm"
include "simplr.mm"
include "ffvelrnd.mm"
include "ptpjcn.mm"
include "fvconst2g.mm"
include "eqeltrd.mm"
include "cnmpt1res.mm"
include "snelpwi.mm"
include "cnima.mm"
include "syl5eqelr.mm"
include "simpllr.mm"
include "f1ocnvfv2.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "ssrab2.mm"
include "a1i.mm"
include "ad3antrrr.mm"
include "f1ocnvfv.mm"
include "simplrr.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "syld.mm"
include "ralrimiva.mm"
include "ralrab.mm"
include "ssrab.mm"
include "mptpreima.mm"
include "syl6sseqr.mm"
include "wfun.mm"
include "cdm.mm"
include "funmpt.mm"
include "dmmpti.mm"
include "funimass3.mm"
include "sylancr.mm"
include "mpbird.mm"
include "eleq2.mm"
include "imaeq2.mm"
include "sseq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "expr.mm"
include "simpr.mm"
include "iscnp.mm"
include "mpbir2and.mm"
include "cncnp.mm"
include "sylan.mm"
include "eleqtrrd.mm"
include "ptcn.mm"
include "grpinvf.mm"
include "feqmptd.mm"
include "symginv.mm"
include "adantl.mm"
include "mpteq2dva.mm"
include "3eltr4d.mm"
include "istgp.mm"

theorem symgtgp
  let cA: class A
  let cG: class G
  let cV: class V
  let vf: setvar f
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  assume symgtgp.g: |- G = ( SymGrp ` A )


  assert |- ( A e. V -> G e. TopGrp )

  proof
    cA
    cV
    wcel
    #
    cG
    cgrp
    wcel
    #
    cG
    ctmd
    wcel
    #
    cG
    cminusg
    cfv
    #
    cG
    ctopn
    cfv
    #
    @4
    ccn
    co
    #
    wcel
    cG
    ctgp
    wcel
    cA
    cG
    cV
    symgtgp.g
    symggrp
    #
    @0
    cG
    cmnd
    wcel
    #
    cG
    ctps
    wcel
    #
    cG
    cplusg
    cfv
    #
    @4
    @4
    ctx
    co
    #
    @4
    ccn
    co
    #
    wcel
    @2
    @0
    @1
    @7
    @6
    cG
    grpmnd
    syl
    @0
    @4
    cG
    cbs
    cfv
    #
    ctopon
    cfv
    #
    wcel
    #
    @8
    @0
    cA
    cA
    cpw
    #
    csn
    cxp
    #
    cpt
    cfv
    #
    @12
    crest
    co
    #
    @4
    @13
    @12
    cG
    cV
    cA
    symgtgp.g
    @12
    eqid
    #
    symgtopn
    #
    @0
    @17
    cA
    cA
    cmap
    co
    #
    ctopon
    cfv
    wcel
    #
    @12
    @21
    wss
    #
    @18
    @13
    wcel
    @0
    @15
    cA
    ctopon
    cfv
    wcel
    #
    @22
    cA
    cV
    distopon
    #
    cA
    @15
    @17
    cV
    cA
    @17
    eqid
    #
    pttoponconst
    mpdan
    #
    @0
    vx
    @12
    @21
    @0
    vx
    cv
    #
    @12
    wcel
    #
    cA
    cA
    @28
    wf1o
    #
    @28
    @21
    wcel
    #
    cA
    @12
    @28
    cG
    cV
    symgtgp.g
    @19
    elsymgbas
    #
    @30
    @31
    @0
    cA
    cA
    @28
    wf
    #
    cA
    cA
    @28
    f1of
    @0
    @31
    @33
    wb
    cA
    cA
    @28
    cV
    cV
    elmapg
    anidms
    syl5ibr
    sylbid
    ssrdv
    #
    @12
    @17
    @21
    resttopon
    syl2anc
    eqeltrrd
    #
    @12
    @4
    cG
    @19
    @4
    eqid
    #
    istps
    sylibr
    @0
    @9
    @10
    @15
    @15
    cxko
    co
    #
    @12
    crest
    co
    #
    ccn
    co
    #
    @11
    @0
    @9
    @10
    @37
    ccn
    co
    #
    wcel
    #
    @9
    @39
    wcel
    #
    @0
    @9
    @38
    @38
    ctx
    co
    #
    @37
    ccn
    co
    #
    @40
    @0
    @9
    vx
    vy
    @12
    @12
    @28
    vy
    cv
    #
    ccom
    #
    cmpt2
    @44
    cA
    @12
    @9
    vx
    vy
    cG
    symgtgp.g
    @19
    @9
    eqid
    #
    symgplusg
    #
    @0
    vx
    vy
    @46
    @37
    @38
    @37
    @37
    @38
    @12
    @15
    @15
    ccn
    co
    #
    @12
    @49
    @38
    eqid
    #
    @0
    @15
    ctop
    wcel
    #
    @51
    @37
    @49
    ctopon
    cfv
    wcel
    #
    cA
    cV
    distop
    #
    @53
    @15
    @15
    @37
    @37
    eqid
    xkotopon
    syl2anc
    #
    @0
    @12
    @21
    @49
    @34
    @0
    @24
    @49
    @21
    wceq
    @25
    cA
    @15
    cV
    cA
    cndis
    mpdan
    sseqtr4d
    #
    @50
    @54
    @55
    @0
    @51
    @15
    ccmp
    cnlly
    wcel
    #
    @51
    vx
    vy
    @49
    @49
    @46
    cmpt2
    #
    @37
    @37
    ctx
    co
    @37
    ccn
    co
    wcel
    @53
    @0
    @15
    ccmp
    clly
    wcel
    @56
    cV
    cA
    disllycmp
    ccmp
    @15
    llynlly
    syl
    @53
    @15
    @15
    @15
    vx
    vy
    @57
    @57
    eqid
    xkococn
    syl3anc
    cnmpt2res
    syl5eqel
    @0
    @43
    @10
    @37
    ccn
    @0
    @38
    @4
    @38
    @4
    ctx
    @0
    @38
    @18
    @4
    @0
    @37
    @17
    @12
    crest
    @51
    @0
    @37
    @17
    wceq
    @53
    cA
    @15
    cV
    xkopt
    mpancom
    #
    oveq1d
    @20
    eqtrd
    #
    @59
    oveq12d
    oveq1d
    eleqtrd
    @0
    @52
    @9
    crn
    @12
    wss
    #
    @12
    @49
    wss
    #
    @41
    @42
    wb
    @54
    @0
    @1
    @12
    @12
    cxp
    #
    @12
    @9
    wf
    @60
    @6
    @12
    @9
    cG
    @19
    cG
    cplusf
    cfv
    #
    @9
    @9
    @62
    wfn
    @63
    @9
    wceq
    vx
    vy
    @12
    @12
    @46
    @9
    @48
    @28
    @45
    vx
    vex
    vy
    vex
    #
    coex
    fnmpt2i
    @12
    @9
    @63
    cG
    @19
    @47
    @63
    eqid
    plusfeq
    ax-mp
    eqcomi
    #
    grpplusf
    @62
    @12
    @9
    frn
    3syl
    @55
    @12
    @9
    @10
    @37
    @49
    cnrest2
    syl3anc
    mpbid
    @0
    @38
    @4
    @10
    ccn
    @59
    oveq2d
    eleqtrd
    @9
    cG
    @4
    @65
    @36
    istmd
    syl3anbrc
    @0
    @3
    @4
    @38
    ccn
    co
    #
    @5
    @0
    @3
    @4
    @37
    ccn
    co
    #
    wcel
    #
    @3
    @66
    wcel
    #
    @0
    vx
    @12
    vy
    cA
    @45
    @28
    ccnv
    #
    cfv
    #
    cmpt
    #
    cmpt
    #
    @4
    @17
    ccn
    co
    @3
    @67
    @0
    vx
    @71
    vy
    @16
    cA
    @4
    @17
    cV
    @12
    @26
    @35
    @0
    id
    @0
    @51
    cA
    ctop
    @16
    wf
    #
    @53
    cA
    @15
    ctop
    fconst6g
    syl
    #
    @0
    @45
    cA
    wcel
    #
    wa
    #
    vx
    @12
    @71
    cmpt
    #
    @4
    @15
    ccn
    co
    #
    @4
    @45
    @16
    cfv
    #
    ccn
    co
    @77
    @78
    @79
    wcel
    #
    @12
    cA
    @78
    wf
    #
    @78
    vf
    cv
    #
    @4
    @15
    ccnp
    co
    cfv
    wcel
    #
    vf
    @12
    wral
    #
    @77
    vx
    @12
    @71
    cA
    @78
    @0
    @29
    @76
    @71
    cA
    wcel
    @0
    @29
    wa
    #
    cA
    cA
    @45
    @70
    @86
    @30
    cA
    cA
    @70
    wf1o
    cA
    cA
    @70
    wf
    @0
    @29
    @30
    @32
    biimpa
    cA
    cA
    @28
    f1ocnv
    cA
    cA
    @70
    f1of
    3syl
    #
    ffvelrnda
    an32s
    @78
    eqid
    #
    fmptd
    #
    @77
    @84
    vf
    @12
    @77
    @83
    @12
    wcel
    #
    wa
    #
    @84
    @82
    @83
    @78
    cfv
    #
    vt
    cv
    #
    wcel
    #
    @83
    vv
    cv
    #
    wcel
    #
    @78
    @95
    cima
    #
    @93
    wss
    #
    wa
    #
    vv
    @4
    wrex
    #
    wi
    #
    vt
    @15
    wral
    #
    @77
    @82
    @90
    @89
    adantr
    @91
    @101
    vt
    @15
    @91
    @93
    @15
    wcel
    #
    wa
    #
    @94
    @45
    @83
    ccnv
    #
    cfv
    #
    @93
    wcel
    #
    @100
    @104
    @92
    @106
    @93
    @90
    @92
    @106
    wceq
    @77
    @103
    vx
    @83
    @71
    @106
    @12
    @78
    vx
    vf
    weq
    @45
    @70
    @105
    @28
    @83
    cnveq
    fveq1d
    @88
    @45
    @105
    fvex
    fvmpt
    ad2antlr
    eleq1d
    @91
    @103
    @107
    @100
    @91
    @103
    @107
    wa
    #
    wa
    #
    @106
    vu
    cv
    #
    cfv
    #
    @45
    wceq
    #
    vu
    @12
    crab
    #
    @4
    wcel
    #
    @83
    @113
    wcel
    #
    @78
    @113
    cima
    #
    @93
    wss
    #
    @100
    @91
    @114
    @108
    @91
    @113
    vu
    @12
    @111
    cmpt
    #
    ccnv
    @45
    csn
    #
    cima
    #
    @4
    @45
    cvv
    wcel
    @120
    @113
    wceq
    @64
    vu
    @12
    @111
    @45
    @118
    cvv
    @118
    eqid
    mptiniseg
    ax-mp
    @91
    @118
    @79
    wcel
    @119
    @15
    wcel
    #
    @120
    @4
    wcel
    @91
    @118
    @18
    @15
    ccn
    co
    #
    @79
    @91
    vu
    @111
    @17
    @18
    @15
    @21
    @12
    @18
    eqid
    @0
    @22
    @76
    @90
    @27
    ad2antrr
    #
    @0
    @23
    @76
    @90
    @34
    ad2antrr
    @91
    vu
    @21
    @111
    cmpt
    #
    vu
    @17
    cuni
    #
    @111
    cmpt
    #
    @17
    @15
    ccn
    co
    #
    @91
    @22
    @21
    @125
    wceq
    @124
    @126
    wceq
    @123
    @21
    @17
    toponuni
    vu
    @21
    @125
    @111
    mpteq1
    3syl
    @91
    @126
    @17
    @106
    @16
    cfv
    #
    ccn
    co
    #
    @127
    @91
    @0
    @74
    @106
    cA
    wcel
    #
    @126
    @129
    wcel
    @0
    @76
    @90
    simpll
    @0
    @74
    @76
    @90
    @75
    ad2antrr
    @91
    cA
    cA
    @45
    @105
    @91
    cA
    cA
    @83
    wf1o
    #
    cA
    cA
    @105
    wf1o
    cA
    cA
    @105
    wf
    @77
    @90
    @131
    @0
    @90
    @131
    wb
    @76
    cA
    @12
    @83
    cG
    cV
    symgtgp.g
    @19
    elsymgbas
    adantr
    biimpa
    #
    cA
    cA
    @83
    f1ocnv
    cA
    cA
    @105
    f1of
    3syl
    @0
    @76
    @90
    simplr
    ffvelrnd
    #
    vu
    cA
    @16
    @106
    @17
    cV
    @125
    @125
    eqid
    @26
    ptpjcn
    syl3anc
    @91
    @128
    @15
    @17
    ccn
    @91
    @51
    @130
    @128
    @15
    wceq
    @0
    @51
    @76
    @90
    @53
    ad2antrr
    @133
    cA
    @15
    @106
    ctop
    fvconst2g
    syl2anc
    oveq2d
    eleqtrd
    eqeltrd
    cnmpt1res
    @0
    @122
    @79
    wceq
    @76
    @90
    @0
    @18
    @4
    @15
    ccn
    @20
    oveq1d
    ad2antrr
    eleqtrd
    @76
    @121
    @0
    @90
    @45
    cA
    snelpwi
    ad2antlr
    @119
    @118
    @4
    @15
    cnima
    syl2anc
    syl5eqelr
    adantr
    @109
    @90
    @106
    @83
    cfv
    #
    @45
    wceq
    #
    @115
    @77
    @90
    @108
    simplr
    @109
    @131
    @76
    @135
    @91
    @131
    @108
    @132
    adantr
    @0
    @76
    @90
    @108
    simpllr
    cA
    cA
    @45
    @83
    f1ocnvfv2
    syl2anc
    @112
    @135
    vu
    @83
    @12
    vu
    vf
    weq
    @111
    @134
    @45
    @106
    @110
    @83
    fveq1
    eqeq1d
    elrab
    sylanbrc
    @109
    @117
    @113
    @78
    ccnv
    @93
    cima
    #
    wss
    #
    @109
    @113
    @71
    @93
    wcel
    #
    vx
    @12
    crab
    #
    @136
    @109
    @113
    @12
    wss
    #
    @138
    vx
    @113
    wral
    #
    @113
    @139
    wss
    @140
    @109
    @112
    vu
    @12
    ssrab2
    a1i
    #
    @109
    @106
    @28
    cfv
    #
    @45
    wceq
    #
    @138
    wi
    #
    vx
    @12
    wral
    @141
    @109
    @145
    vx
    @12
    @109
    @29
    wa
    #
    @144
    @71
    @106
    wceq
    #
    @138
    @146
    @30
    @130
    @144
    @147
    wi
    @109
    @29
    @30
    @0
    @29
    @30
    wb
    @76
    @90
    @108
    @32
    ad3antrrr
    biimpa
    @91
    @130
    @108
    @29
    @133
    ad2antrr
    cA
    cA
    @106
    @45
    @28
    f1ocnvfv
    syl2anc
    @146
    @138
    @147
    @107
    @91
    @103
    @107
    @29
    simplrr
    @71
    @106
    @93
    eleq1
    syl5ibrcom
    syld
    ralrimiva
    @112
    @144
    @138
    vx
    vu
    @12
    vu
    vx
    weq
    @111
    @143
    @45
    @106
    @110
    @28
    fveq1
    eqeq1d
    ralrab
    sylibr
    @138
    vx
    @12
    @113
    ssrab
    sylanbrc
    vx
    @12
    @71
    @93
    @78
    @88
    mptpreima
    syl6sseqr
    @109
    @78
    wfun
    @113
    @78
    cdm
    #
    wss
    @117
    @137
    wb
    vx
    @12
    @71
    funmpt
    @109
    @113
    @12
    @148
    @142
    vx
    @12
    @71
    @78
    @45
    @70
    fvex
    @88
    dmmpti
    syl6sseqr
    @113
    @93
    @78
    funimass3
    sylancr
    mpbird
    @99
    @115
    @117
    wa
    vv
    @113
    @4
    @95
    @113
    wceq
    #
    @96
    @115
    @98
    @117
    @95
    @113
    @83
    eleq2
    @149
    @97
    @116
    @93
    @95
    @113
    @78
    imaeq2
    sseq1d
    anbi12d
    rspcev
    syl12anc
    expr
    sylbid
    ralrimiva
    @91
    @14
    @24
    @90
    @84
    @82
    @102
    wa
    wb
    @0
    @14
    @76
    @90
    @35
    ad2antrr
    @0
    @24
    @76
    @90
    @25
    ad2antrr
    @77
    @90
    simpr
    vv
    vt
    @83
    @78
    @4
    @15
    @12
    cA
    iscnp
    syl3anc
    mpbir2and
    ralrimiva
    @0
    @81
    @82
    @85
    wa
    wb
    #
    @76
    @0
    @14
    @24
    @150
    @35
    @25
    vf
    @78
    @4
    @15
    @12
    cA
    cncnp
    syl2anc
    adantr
    mpbir2and
    @77
    @80
    @15
    @4
    ccn
    @0
    @51
    @76
    @80
    @15
    wceq
    @53
    cA
    @15
    @45
    ctop
    fvconst2g
    sylan
    oveq2d
    eleqtrrd
    ptcn
    @0
    @3
    vx
    @12
    @28
    @3
    cfv
    #
    cmpt
    @73
    @0
    vx
    @12
    @12
    @3
    @0
    @1
    @12
    @12
    @3
    wf
    #
    @6
    @12
    cG
    @3
    @19
    @3
    eqid
    #
    grpinvf
    #
    syl
    feqmptd
    @0
    vx
    @12
    @151
    @72
    @86
    @151
    @70
    @72
    @29
    @151
    @70
    wceq
    @0
    cA
    @12
    @28
    cG
    @3
    symgtgp.g
    @19
    @153
    symginv
    adantl
    @86
    vy
    cA
    cA
    @70
    @87
    feqmptd
    eqtrd
    mpteq2dva
    eqtrd
    @0
    @37
    @17
    @4
    ccn
    @58
    oveq2d
    3eltr4d
    @0
    @52
    @3
    crn
    @12
    wss
    #
    @61
    @68
    @69
    wb
    @54
    @0
    @1
    @152
    @155
    @6
    @154
    @12
    @12
    @3
    frn
    3syl
    @55
    @12
    @3
    @4
    @37
    @49
    cnrest2
    syl3anc
    mpbid
    @0
    @38
    @4
    @4
    ccn
    @59
    oveq2d
    eleqtrd
    cG
    @3
    @4
    @36
    @153
    istgp
    syl3anbrc
end
