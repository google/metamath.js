include "cpt.mm"
include "cfv.mm"
include "cuni.mm"
include "csn.mm"
include "cv.mm"
include "cmpt.mm"
include "ccnv.mm"
include "cima.mm"
include "cmpt2.mm"
include "crn.mm"
include "cun.mm"
include "cfi.mm"
include "cixp.mm"
include "crest.mm"
include "co.mm"
include "ctg.mm"
include "firest.mm"
include "cin.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "snex.mm"
include "wral.mm"
include "fvex.mm"
include "rgenw.mm"
include "eqid.mm"
include "mpt2exxg.mm"
include "sylancl.mm"
include "rnexg.mm"
include "syl.mm"
include "unexg.mm"
include "sylancr.mm"
include "ralrimiva.mm"
include "ixpexg.mm"
include "restval.mm"
include "syl2anc.mm"
include "mptun.mm"
include "rneqi.mm"
include "rnun.mm"
include "eqtri.mm"
include "cop.mm"
include "elsni.mm"
include "ineq1d.mm"
include "mpteq2ia.mm"
include "uniex.mm"
include "inex1.mm"
include "fmptsn.mm"
include "mp2an.mm"
include "eqtr4i.mm"
include "rnsnop.mm"
include "wa.mm"
include "ctop.mm"
include "wss.mm"
include "ffvelrnda.mm"
include "inss1.mm"
include "restuni.mm"
include "restin.mm"
include "incom.mm"
include "oveq2i.mm"
include "syl6eq.mm"
include "unieqd.mm"
include "eqtr4d.mm"
include "ixpeq2dva.mm"
include "ixpin.mm"
include "csb.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nfov.mm"
include "nfuni.mm"
include "weq.mm"
include "fveq2.mm"
include "csbeq1a.mm"
include "oveq12d.mm"
include "cbvixp.mm"
include "ixpeq2.mm"
include "ovex.mm"
include "fvmptf.mm"
include "mpan2.mm"
include "mprg.mm"
include "3eqtr3g.mm"
include "wf.mm"
include "ptuni.mm"
include "resttop.mm"
include "fmptd.mm"
include "3eqtr3d.mm"
include "sneqd.mm"
include "syl5eq.mm"
include "wrex.mm"
include "cab.mm"
include "wfn.mm"
include "vex.mm"
include "elixp.mm"
include "simprbi.mm"
include "nfel2.mm"
include "eleq12d.mm"
include "rspc.mm"
include "syl5.mm"
include "pm4.71d.mm"
include "anbi2d.mm"
include "an4.mm"
include "elin.mm"
include "anbi2i.mm"
include "bitr4i.mm"
include "syl6bb.mm"
include "eleq2d.mm"
include "syl5bbr.mm"
include "anbi1d.mm"
include "sylan9bbr.mm"
include "abbidv.mm"
include "crab.mm"
include "mptpreima.mm"
include "df-rab.mm"
include "eqtr2i.mm"
include "abid2.mm"
include "ineq12i.mm"
include "inab.mm"
include "eqtr3i.mm"
include "3eqtr4g.mm"
include "eqeq2d.mm"
include "rexbidv.mm"
include "ineq1.mm"
include "imaeq2d.mm"
include "cbvrexv.mm"
include "a1i.mm"
include "adantl.mm"
include "wb.mm"
include "wi.mm"
include "nfv.mm"
include "nfel.mm"
include "nfim.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "chvar.mm"
include "elrest.mm"
include "bitrd.mm"
include "imaeq2.mm"
include "rexxfr2d.mm"
include "bitr4d.mm"
include "rexbidva.mm"
include "rnmpt.mm"
include "nfre1.mm"
include "mptex.mm"
include "cnvex.mm"
include "imaexg.mm"
include "ax-mp.mm"
include "rgen2w.mm"
include "rexrnmpt2.mm"
include "eqeq1.mm"
include "2rexbidv.mm"
include "syl5bb.mm"
include "cbvab.mm"
include "rnmpt2.mm"
include "uneq12d.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "syl5eqr.mm"
include "ptval2.mm"
include "oveq1d.mm"
include "tgrest.mm"
include "3eqtr4d.mm"

theorem ptrest
  let wph: wff ph
  let cA: class A
  let cS: class S
  let vk: setvar k
  let cF: class F
  let cV: class V
  let cW: class W
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  assume ptrest.0: |- ( ph -> A e. V )
  assume ptrest.1: |- ( ph -> F : A --> Top )
  assume ptrest.2: |- ( ( ph /\ k e. A ) -> S e. W )

  disjoint k ph
  disjoint A k
  disjoint F k
  disjoint V k
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint ph u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint ph v
  disjoint w x
  disjoint w y
  disjoint ph w
  disjoint x y
  disjoint ph x
  disjoint ph y
  disjoint A u
  disjoint A v
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint V u
  disjoint V v
  disjoint V w
  disjoint V x
  disjoint V y
  disjoint W u
  disjoint W v
  disjoint W w
  disjoint W x
  disjoint W y
  assert |- ( ph -> ( ( Xt_ ` F ) |`t X_ k e. A S ) = ( Xt_ ` ( k e. A |-> ( ( F ` k ) |`t S ) ) ) )

  proof
    wph
    cF
    cpt
    cfv
    #
    cuni
    #
    csn
    #
    vu
    vv
    cA
    vu
    cv
    #
    cF
    cfv
    #
    vw
    @1
    @3
    vw
    cv
    #
    cfv
    #
    cmpt
    #
    ccnv
    #
    vv
    cv
    #
    cima
    #
    cmpt2
    #
    crn
    #
    cun
    #
    cfi
    cfv
    #
    vk
    cA
    cS
    cixp
    #
    crest
    co
    #
    ctg
    cfv
    #
    vk
    cA
    vk
    cv
    #
    cF
    cfv
    #
    cS
    crest
    co
    #
    cmpt
    #
    cpt
    cfv
    #
    cuni
    #
    csn
    #
    vu
    vv
    cA
    @3
    @21
    cfv
    #
    vw
    @23
    @6
    cmpt
    #
    ccnv
    #
    @9
    cima
    #
    cmpt2
    #
    crn
    #
    cun
    #
    cfi
    cfv
    #
    ctg
    cfv
    #
    @0
    @15
    crest
    co
    #
    @22
    wph
    @16
    @32
    ctg
    wph
    @16
    @13
    @15
    crest
    co
    #
    cfi
    cfv
    @32
    @15
    @13
    firest
    wph
    @35
    @31
    cfi
    wph
    @35
    vx
    @13
    vx
    cv
    #
    @15
    cin
    #
    cmpt
    #
    crn
    #
    @31
    wph
    @13
    cvv
    wcel
    #
    @15
    cvv
    wcel
    #
    @35
    @39
    wceq
    wph
    @2
    cvv
    wcel
    @12
    cvv
    wcel
    #
    @40
    @1
    snex
    wph
    @11
    cvv
    wcel
    #
    @42
    wph
    cA
    cV
    wcel
    #
    @4
    cvv
    wcel
    #
    vu
    cA
    wral
    @43
    ptrest.0
    @45
    vu
    cA
    @3
    cF
    fvex
    #
    rgenw
    vu
    vv
    cA
    @4
    @10
    cV
    cvv
    @11
    @11
    eqid
    #
    mpt2exxg
    sylancl
    @11
    cvv
    rnexg
    syl
    @2
    @12
    cvv
    cvv
    unexg
    sylancr
    wph
    cS
    cW
    wcel
    #
    vk
    cA
    wral
    @41
    wph
    @48
    vk
    cA
    ptrest.2
    ralrimiva
    vk
    cA
    cS
    cW
    ixpexg
    syl
    #
    vx
    @15
    @13
    cvv
    cvv
    restval
    syl2anc
    wph
    @39
    vx
    @2
    @37
    cmpt
    #
    crn
    #
    vx
    @12
    @37
    cmpt
    #
    crn
    #
    cun
    #
    @31
    @39
    @50
    @52
    cun
    #
    crn
    @54
    @38
    @55
    vx
    @2
    @12
    @37
    mptun
    rneqi
    @50
    @52
    rnun
    eqtri
    wph
    @51
    @24
    @53
    @30
    wph
    @51
    @1
    @15
    cin
    #
    csn
    #
    @24
    @51
    @1
    @56
    cop
    csn
    #
    crn
    @57
    @50
    @58
    @50
    vx
    @2
    @56
    cmpt
    #
    @58
    vx
    @2
    @37
    @56
    @36
    @2
    wcel
    @36
    @1
    @15
    @36
    @1
    elsni
    ineq1d
    mpteq2ia
    @1
    cvv
    wcel
    @56
    cvv
    wcel
    @58
    @59
    wceq
    @0
    cF
    cpt
    fvex
    uniex
    #
    @1
    @15
    @60
    inex1
    vx
    @1
    @56
    cvv
    cvv
    fmptsn
    mp2an
    eqtr4i
    rneqi
    @1
    @56
    @60
    rnsnop
    eqtri
    wph
    @56
    @23
    wph
    vk
    cA
    @19
    cuni
    #
    cixp
    #
    @15
    cin
    #
    vy
    cA
    vy
    cv
    #
    @21
    cfv
    #
    cuni
    #
    cixp
    #
    @56
    @23
    wph
    vk
    cA
    @61
    cS
    cin
    #
    cixp
    vk
    cA
    @20
    cuni
    #
    cixp
    #
    @63
    @67
    wph
    vk
    cA
    @68
    @69
    wph
    @18
    cA
    wcel
    #
    wa
    #
    @68
    @19
    @68
    crest
    co
    #
    cuni
    #
    @69
    @72
    @19
    ctop
    wcel
    #
    @68
    @61
    wss
    @68
    @74
    wceq
    wph
    cA
    ctop
    @18
    cF
    ptrest.1
    ffvelrnda
    #
    @61
    cS
    inss1
    @68
    @19
    @61
    @61
    eqid
    #
    restuni
    sylancl
    @72
    @20
    @73
    @72
    @20
    @19
    cS
    @61
    cin
    #
    crest
    co
    #
    @73
    @72
    @19
    cvv
    wcel
    @48
    @20
    @79
    wceq
    @18
    cF
    fvex
    ptrest.2
    cS
    @19
    cvv
    cW
    @61
    @77
    restin
    sylancr
    @78
    @68
    @19
    crest
    cS
    @61
    incom
    oveq2i
    syl6eq
    unieqd
    eqtr4d
    ixpeq2dva
    vk
    cA
    @61
    cS
    ixpin
    @70
    vy
    cA
    @64
    cF
    cfv
    #
    vk
    @64
    cS
    csb
    #
    crest
    co
    #
    cuni
    #
    cixp
    #
    @67
    vk
    vy
    cA
    @69
    @83
    vy
    @69
    nfcv
    vk
    @82
    vk
    @80
    @81
    crest
    vk
    @80
    nfcv
    vk
    crest
    nfcv
    #
    vk
    @64
    cS
    nfcsb1v
    nfov
    #
    nfuni
    vk
    vy
    weq
    #
    @20
    @82
    @87
    @19
    @80
    cS
    @81
    crest
    @18
    @64
    cF
    fveq2
    vk
    @64
    cS
    csbeq1a
    oveq12d
    #
    unieqd
    cbvixp
    @66
    @83
    wceq
    @67
    @84
    wceq
    vy
    cA
    vy
    cA
    @66
    @83
    ixpeq2
    @64
    cA
    wcel
    #
    @65
    @82
    @89
    @82
    cvv
    wcel
    @65
    @82
    wceq
    @80
    @81
    crest
    ovex
    vk
    @64
    @20
    @82
    cA
    @21
    cvv
    vk
    @64
    nfcv
    @86
    @88
    @21
    eqid
    #
    fvmptf
    mpan2
    unieqd
    mprg
    eqtr4i
    3eqtr3g
    wph
    @62
    @1
    @15
    wph
    @44
    cA
    ctop
    cF
    wf
    #
    @62
    @1
    wceq
    ptrest.0
    ptrest.1
    vk
    cA
    cF
    @0
    cV
    @0
    eqid
    #
    ptuni
    syl2anc
    ineq1d
    wph
    @44
    cA
    ctop
    @21
    wf
    #
    @67
    @23
    wceq
    ptrest.0
    wph
    vk
    cA
    @20
    ctop
    @21
    @72
    @75
    @48
    @20
    ctop
    wcel
    @76
    ptrest.2
    cS
    @19
    cW
    resttop
    syl2anc
    @90
    fmptd
    #
    vy
    cA
    @21
    @22
    cV
    @22
    eqid
    #
    ptuni
    syl2anc
    3eqtr3d
    #
    sneqd
    syl5eq
    wph
    @36
    @10
    @15
    cin
    #
    wceq
    #
    vv
    @4
    wrex
    #
    vu
    cA
    wrex
    #
    vx
    cab
    #
    @36
    @28
    wceq
    #
    vv
    @25
    wrex
    #
    vu
    cA
    wrex
    #
    vx
    cab
    @53
    @30
    wph
    @100
    @104
    vx
    wph
    @99
    @103
    vu
    cA
    wph
    @3
    cA
    wcel
    #
    wa
    #
    @99
    @36
    @27
    @64
    vk
    @3
    cS
    csb
    #
    cin
    #
    cima
    #
    wceq
    #
    vy
    @4
    wrex
    #
    @103
    @106
    @99
    @36
    @27
    @9
    @107
    cin
    #
    cima
    #
    wceq
    #
    vv
    @4
    wrex
    @111
    @106
    @98
    @114
    vv
    @4
    @106
    @97
    @113
    @36
    @106
    @5
    @1
    wcel
    #
    @6
    @9
    wcel
    #
    wa
    #
    @5
    @15
    wcel
    #
    wa
    #
    vw
    cab
    #
    @5
    @23
    wcel
    #
    @6
    @112
    wcel
    #
    wa
    #
    vw
    cab
    #
    @97
    @113
    @106
    @119
    @123
    vw
    @105
    @119
    @115
    @118
    wa
    #
    @122
    wa
    #
    wph
    @123
    @105
    @119
    @117
    @118
    @6
    @107
    wcel
    #
    wa
    #
    wa
    #
    @126
    @105
    @118
    @128
    @117
    @105
    @118
    @127
    @118
    @18
    @5
    cfv
    #
    cS
    wcel
    #
    vk
    cA
    wral
    #
    @105
    @127
    @118
    @5
    cA
    wfn
    @132
    vk
    cA
    cS
    @5
    vw
    vex
    elixp
    simprbi
    @131
    @127
    vk
    @3
    cA
    vk
    @6
    @107
    vk
    @3
    cS
    nfcsb1v
    #
    nfel2
    vk
    vu
    weq
    #
    @130
    @6
    cS
    @107
    @18
    @3
    @5
    fveq2
    vk
    @3
    cS
    csbeq1a
    #
    eleq12d
    rspc
    syl5
    pm4.71d
    anbi2d
    @129
    @125
    @116
    @127
    wa
    #
    wa
    @126
    @115
    @116
    @118
    @127
    an4
    @122
    @136
    @125
    @6
    @9
    @107
    elin
    anbi2i
    bitr4i
    syl6bb
    wph
    @125
    @121
    @122
    @125
    @5
    @56
    wcel
    wph
    @121
    @5
    @1
    @15
    elin
    wph
    @56
    @23
    @5
    @96
    eleq2d
    syl5bbr
    anbi1d
    sylan9bbr
    abbidv
    @117
    vw
    cab
    #
    @118
    vw
    cab
    #
    cin
    @97
    @120
    @137
    @10
    @138
    @15
    @10
    @116
    vw
    @1
    crab
    @137
    vw
    @1
    @6
    @9
    @7
    @7
    eqid
    mptpreima
    @116
    vw
    @1
    df-rab
    eqtr2i
    vw
    @15
    abid2
    ineq12i
    @117
    @118
    vw
    inab
    eqtr3i
    @113
    @122
    vw
    @23
    crab
    @124
    vw
    @23
    @6
    @112
    @26
    @26
    eqid
    mptpreima
    @122
    vw
    @23
    df-rab
    eqtri
    3eqtr4g
    eqeq2d
    rexbidv
    @114
    @110
    vv
    vy
    @4
    vv
    vy
    weq
    #
    @113
    @109
    @36
    @139
    @112
    @108
    @27
    @9
    @64
    @107
    ineq1
    imaeq2d
    eqeq2d
    cbvrexv
    syl6bb
    @106
    @102
    @110
    vv
    vy
    @108
    @25
    @4
    cvv
    @108
    cvv
    wcel
    @106
    @64
    @4
    wcel
    wa
    @64
    @107
    vy
    vex
    inex1
    a1i
    @106
    @9
    @25
    wcel
    @9
    @4
    @107
    crest
    co
    #
    wcel
    #
    @9
    @108
    wceq
    #
    vy
    @4
    wrex
    #
    @106
    @25
    @140
    @9
    @105
    @25
    @140
    wceq
    #
    wph
    @105
    @140
    cvv
    wcel
    @144
    @4
    @107
    crest
    ovex
    vk
    @3
    @20
    @140
    cA
    @21
    cvv
    vk
    @3
    nfcv
    vk
    @4
    @107
    crest
    vk
    @4
    nfcv
    @85
    @133
    nfov
    @134
    @19
    @4
    cS
    @107
    crest
    @18
    @3
    cF
    fveq2
    @135
    oveq12d
    @90
    fvmptf
    mpan2
    adantl
    eleq2d
    @106
    @45
    @107
    vk
    @3
    cW
    csb
    #
    wcel
    #
    @141
    @143
    wb
    @46
    @72
    @48
    wi
    @106
    @146
    wi
    vk
    vu
    @106
    @146
    vk
    @106
    vk
    nfv
    vk
    @107
    @145
    @133
    vk
    @3
    cW
    nfcsb1v
    nfel
    nfim
    @134
    @72
    @106
    @48
    @146
    @134
    @71
    @105
    wph
    @18
    @3
    cA
    eleq1
    anbi2d
    @134
    cS
    @107
    cW
    @145
    @135
    vk
    @3
    cW
    csbeq1a
    eleq12d
    imbi12d
    ptrest.2
    chvar
    vy
    @9
    @107
    @4
    cvv
    @145
    elrest
    sylancr
    bitrd
    @142
    @102
    @110
    wb
    @106
    @142
    @28
    @109
    @36
    @9
    @108
    @27
    imaeq2
    eqeq2d
    adantl
    rexxfr2d
    bitr4d
    rexbidva
    abbidv
    @53
    @64
    @37
    wceq
    #
    vx
    @12
    wrex
    #
    vy
    cab
    @101
    vx
    vy
    @12
    @37
    @52
    @52
    eqid
    rnmpt
    @148
    @100
    vy
    vx
    @147
    vx
    @12
    nfre1
    @100
    vy
    nfv
    @148
    @64
    @97
    wceq
    #
    vv
    @4
    wrex
    vu
    cA
    wrex
    #
    vy
    vx
    weq
    #
    @100
    @10
    cvv
    wcel
    #
    vv
    @4
    wral
    vu
    cA
    wral
    @148
    @150
    wb
    @152
    vu
    vv
    cA
    @4
    @8
    cvv
    wcel
    @152
    @7
    vw
    @1
    @6
    @60
    mptex
    cnvex
    @8
    @9
    cvv
    imaexg
    ax-mp
    rgen2w
    @147
    @149
    vu
    vv
    vx
    cA
    @4
    @10
    @11
    cvv
    @47
    @36
    @10
    wceq
    @37
    @97
    @64
    @36
    @10
    @15
    ineq1
    eqeq2d
    rexrnmpt2
    ax-mp
    @151
    @149
    @98
    vu
    vv
    cA
    @4
    @64
    @36
    @97
    eqeq1
    2rexbidv
    syl5bb
    cbvab
    eqtri
    vu
    vv
    vx
    cA
    @25
    @28
    @29
    @29
    eqid
    #
    rnmpt2
    3eqtr4g
    uneq12d
    syl5eq
    eqtrd
    fveq2d
    syl5eqr
    fveq2d
    wph
    @34
    @14
    ctg
    cfv
    #
    @15
    crest
    co
    #
    @17
    wph
    @0
    @154
    @15
    crest
    wph
    @44
    @91
    @0
    @154
    wceq
    ptrest.0
    ptrest.1
    vw
    vv
    cA
    vu
    cF
    @11
    @0
    cV
    @1
    @92
    @1
    eqid
    @47
    ptval2
    syl2anc
    oveq1d
    wph
    @14
    cvv
    wcel
    @41
    @17
    @155
    wceq
    @13
    cfi
    fvex
    @49
    @15
    @14
    cvv
    cvv
    tgrest
    sylancr
    eqtr4d
    wph
    @44
    @93
    @22
    @33
    wceq
    ptrest.0
    @94
    vw
    vv
    cA
    vu
    @21
    @29
    @22
    cV
    @23
    @95
    @23
    eqid
    @153
    ptval2
    syl2anc
    3eqtr4d
end
