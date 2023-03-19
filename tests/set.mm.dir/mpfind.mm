include "cab.mm"
include "wcel.mm"
include "cv.mm"
include "ces.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "cress.mm"
include "cmpl.mm"
include "cbs.mm"
include "wrex.mm"
include "crn.mm"
include "syl6eleq.mm"
include "wfn.mm"
include "wb.mm"
include "cmap.mm"
include "cpws.mm"
include "wf.mm"
include "crh.mm"
include "cvv.mm"
include "ccrg.mm"
include "csubrg.mm"
include "w3a.mm"
include "mpfrcl.mm"
include "syl.mm"
include "eqid.mm"
include "evlsrhm.mm"
include "rhmf.mm"
include "ffn.mm"
include "fvelrnb.mm"
include "mpbid.mm"
include "wa.mm"
include "wfun.mm"
include "ccnv.mm"
include "cima.mm"
include "ffun.mm"
include "adantr.mm"
include "cascl.mm"
include "cplusg.mm"
include "cmulr.mm"
include "cmvr.mm"
include "crg.mm"
include "simp1d.mm"
include "simp2d.mm"
include "simp3d.mm"
include "subrgcrng.mm"
include "syl2anc.mm"
include "crngring.mm"
include "mplring.mm"
include "simprl.mm"
include "elpreima.mm"
include "simpld.mm"
include "simprr.mm"
include "ringacl.mm"
include "syl3anc.mm"
include "cof.mm"
include "cghm.mm"
include "rhmghm.mm"
include "ghmlin.mm"
include "ovexd.mm"
include "ffvelrnd.mm"
include "pwsplusgval.mm"
include "eqtrd.mm"
include "simpl.mm"
include "fnfvelrn.mm"
include "syl6eleqr.mm"
include "fvimacnvi.mm"
include "jca.mm"
include "wi.mm"
include "fvex.mm"
include "eleq1.mm"
include "vex.mm"
include "elab.mm"
include "syl5bbr.mm"
include "anbi12d.mm"
include "bi2anan9.mm"
include "anbi2d.mm"
include "ovex.mm"
include "oveq12.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "vtocl2.mm"
include "syl12anc.mm"
include "eqeltrd.mm"
include "mpbir2and.mm"
include "adantlr.mm"
include "ringcl.mm"
include "cmgp.mm"
include "cmhm.mm"
include "rhmmhm.mm"
include "mgpbas.mm"
include "mgpplusg.mm"
include "mhmlin.mm"
include "pwsmulrval.mm"
include "csca.mm"
include "casa.mm"
include "mplassa.mm"
include "asclrhm.mm"
include "mplsca.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "csn.mm"
include "cxp.mm"
include "wss.mm"
include "subrgss.mm"
include "ressbas2.mm"
include "biimpar.mm"
include "evlssca.mm"
include "wral.mm"
include "ralrimiva.mm"
include "snex.mm"
include "xpex.mm"
include "sneq.mm"
include "xpeq2d.mm"
include "cbvralv.mm"
include "sylib.mm"
include "r19.21bi.mm"
include "syldan.mm"
include "simpr.mm"
include "mvrcl.mm"
include "cmpt.mm"
include "evlsvar.mm"
include "mptex.mm"
include "sylibr.mm"
include "fveq2.mm"
include "mpteq2dv.mm"
include "mplind.mm"
include "syl5ibcom.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "elabg.mm"

theorem mpfind
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  let wsi: wff si
  let wrh: wff rh
  let vx: setvar x
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let vf: setvar f
  let vg: setvar g
  let cI: class I
  let vi: setvar i
  let vj: setvar j
  let vy: setvar y
  assume mpfind.cb: |- B = ( Base ` S )
  assume mpfind.cp: |- .+ = ( +g ` S )
  assume mpfind.ct: |- .x. = ( .r ` S )
  assume mpfind.cq: |- Q = ran ( ( I evalSub S ) ` R )
  assume mpfind.ad: |- ( ( ph /\ ( ( f e. Q /\ ta ) /\ ( g e. Q /\ et ) ) ) -> ze )
  assume mpfind.mu: |- ( ( ph /\ ( ( f e. Q /\ ta ) /\ ( g e. Q /\ et ) ) ) -> si )
  assume mpfind.wa: |- ( x = ( ( B ^m I ) X. { f } ) -> ( ps <-> ch ) )
  assume mpfind.wb: |- ( x = ( g e. ( B ^m I ) |-> ( g ` f ) ) -> ( ps <-> th ) )
  assume mpfind.wc: |- ( x = f -> ( ps <-> ta ) )
  assume mpfind.wd: |- ( x = g -> ( ps <-> et ) )
  assume mpfind.we: |- ( x = ( f oF .+ g ) -> ( ps <-> ze ) )
  assume mpfind.wf: |- ( x = ( f oF .x. g ) -> ( ps <-> si ) )
  assume mpfind.wg: |- ( x = A -> ( ps <-> rh ) )
  assume mpfind.co: |- ( ( ph /\ f e. R ) -> ch )
  assume mpfind.pr: |- ( ( ph /\ f e. I ) -> th )
  assume mpfind.a: |- ( ph -> A e. Q )

  disjoint ch x
  disjoint et x
  disjoint f ph
  disjoint g ph
  disjoint f g
  disjoint f ps
  disjoint g ps
  disjoint rh x
  disjoint si x
  disjoint ta x
  disjoint th x
  disjoint x ze
  disjoint A x
  disjoint B f
  disjoint B g
  disjoint B x
  disjoint f x
  disjoint g x
  disjoint I f
  disjoint I g
  disjoint I x
  disjoint .+ f
  disjoint .+ g
  disjoint .+ x
  disjoint Q f
  disjoint Q g
  disjoint R f
  disjoint R g
  disjoint S f
  disjoint S g
  disjoint .x. f
  disjoint .x. g
  disjoint .x. x
  disjoint ch i
  disjoint i x
  disjoint i ph
  disjoint j ph
  disjoint f i
  disjoint f j
  disjoint g i
  disjoint g j
  disjoint i j
  disjoint ph y
  disjoint i ps
  disjoint j ps
  disjoint ps y
  disjoint A y
  disjoint x y
  disjoint B i
  disjoint I i
  disjoint I j
  disjoint j x
  disjoint I y
  disjoint R i
  disjoint R j
  disjoint R y
  disjoint S i
  disjoint S j
  disjoint S y
  disjoint i y
  disjoint j y
  assert |- ( ph -> rh )

  proof
    wph
    cA
    wps
    vx
    cab
    #
    wcel
    #
    wrh
    wph
    vy
    cv
    #
    cR
    cI
    cS
    ces
    co
    cfv
    #
    cfv
    #
    cA
    wceq
    #
    vy
    cI
    cS
    cR
    cress
    co
    #
    cmpl
    co
    #
    cbs
    cfv
    #
    wrex
    #
    @1
    wph
    cA
    @3
    crn
    #
    wcel
    #
    @9
    wph
    cA
    cQ
    @10
    mpfind.a
    mpfind.cq
    syl6eleq
    wph
    @3
    @8
    wfn
    #
    @11
    @9
    wb
    wph
    @8
    cS
    cB
    cI
    cmap
    co
    #
    cpws
    co
    #
    cbs
    cfv
    #
    @3
    wf
    #
    @12
    wph
    @3
    @7
    @14
    crh
    co
    wcel
    #
    @16
    wph
    cI
    cvv
    wcel
    #
    cS
    ccrg
    wcel
    #
    cR
    cS
    csubrg
    cfv
    wcel
    #
    w3a
    #
    @17
    wph
    cA
    cQ
    wcel
    #
    @21
    mpfind.a
    cQ
    cR
    cS
    cI
    cA
    mpfind.cq
    mpfrcl
    syl
    #
    cB
    @3
    cR
    cS
    @14
    @6
    cI
    cvv
    @7
    @3
    eqid
    #
    @7
    eqid
    #
    @6
    eqid
    #
    @14
    eqid
    #
    mpfind.cb
    evlsrhm
    syl
    #
    @8
    @15
    @7
    @14
    @3
    @8
    eqid
    #
    @15
    eqid
    #
    rhmf
    syl
    #
    @8
    @15
    @3
    ffn
    syl
    #
    vy
    @8
    cA
    @3
    fvelrnb
    syl
    mpbid
    wph
    @5
    @1
    vy
    @8
    wph
    @2
    @8
    wcel
    #
    wa
    #
    @4
    @0
    wcel
    #
    @5
    @1
    @34
    @3
    wfun
    #
    @2
    @3
    ccnv
    @0
    cima
    #
    wcel
    @35
    wph
    @36
    @33
    wph
    @16
    @36
    @31
    @8
    @15
    @3
    ffun
    syl
    #
    adantr
    @34
    vi
    vj
    @8
    @7
    cascl
    cfv
    #
    @7
    cplusg
    cfv
    #
    @6
    @7
    cmulr
    cfv
    #
    @37
    cI
    @6
    cbs
    cfv
    #
    cI
    @6
    cmvr
    co
    #
    @2
    @7
    @42
    eqid
    @43
    eqid
    #
    @25
    @40
    eqid
    #
    @41
    eqid
    #
    @39
    eqid
    #
    @29
    wph
    vi
    cv
    #
    @37
    wcel
    #
    vj
    cv
    #
    @37
    wcel
    #
    wa
    #
    @48
    @50
    @40
    co
    #
    @37
    wcel
    #
    @33
    wph
    @52
    wa
    #
    @54
    @53
    @8
    wcel
    #
    @53
    @3
    cfv
    #
    @0
    wcel
    #
    @55
    @7
    crg
    wcel
    #
    @48
    @8
    wcel
    #
    @50
    @8
    wcel
    #
    @56
    wph
    @59
    @52
    wph
    @18
    @6
    crg
    wcel
    #
    @59
    wph
    @18
    @19
    @20
    @23
    simp1d
    #
    wph
    @6
    ccrg
    wcel
    #
    @62
    wph
    @19
    @20
    @64
    wph
    @18
    @19
    @20
    @23
    simp2d
    #
    wph
    @18
    @19
    @20
    @23
    simp3d
    #
    cR
    cS
    @6
    @26
    subrgcrng
    syl2anc
    #
    @6
    crngring
    syl
    #
    @7
    @6
    cI
    cvv
    @25
    mplring
    syl2anc
    adantr
    #
    @55
    @60
    @48
    @3
    cfv
    #
    @0
    wcel
    #
    @55
    @49
    @60
    @71
    wa
    #
    wph
    @49
    @51
    simprl
    #
    wph
    @49
    @72
    wb
    #
    @52
    wph
    @12
    @74
    @32
    @8
    @48
    @0
    @3
    elpreima
    syl
    adantr
    mpbid
    simpld
    #
    @55
    @61
    @50
    @3
    cfv
    #
    @0
    wcel
    #
    @55
    @51
    @61
    @77
    wa
    #
    wph
    @49
    @51
    simprr
    #
    wph
    @51
    @78
    wb
    #
    @52
    wph
    @12
    @80
    @32
    @8
    @50
    @0
    @3
    elpreima
    syl
    adantr
    mpbid
    simpld
    #
    @8
    @40
    @7
    @48
    @50
    @29
    @45
    ringacl
    syl3anc
    @55
    @57
    @70
    @76
    c.pl
    cof
    #
    co
    #
    @0
    @55
    @57
    @70
    @76
    @14
    cplusg
    cfv
    #
    co
    #
    @83
    @55
    @3
    @7
    @14
    cghm
    co
    wcel
    #
    @60
    @61
    @57
    @85
    wceq
    wph
    @86
    @52
    wph
    @17
    @86
    @28
    @7
    @14
    @3
    rhmghm
    syl
    adantr
    @75
    @81
    @40
    @84
    @7
    @14
    @48
    @3
    @50
    @8
    @29
    @45
    @84
    eqid
    #
    ghmlin
    syl3anc
    @55
    @15
    c.pl
    @84
    cS
    @70
    @76
    @13
    ccrg
    cvv
    @14
    @27
    @30
    wph
    @19
    @52
    @65
    adantr
    #
    @55
    cB
    cI
    cmap
    ovexd
    #
    @55
    @8
    @15
    @48
    @3
    wph
    @16
    @52
    @31
    adantr
    #
    @75
    ffvelrnd
    #
    @55
    @8
    @15
    @50
    @3
    @90
    @81
    ffvelrnd
    #
    mpfind.cp
    @87
    pwsplusgval
    eqtrd
    @55
    wph
    @70
    cQ
    wcel
    #
    @71
    wa
    #
    @76
    cQ
    wcel
    #
    @77
    wa
    #
    @83
    @0
    wcel
    #
    wph
    @52
    simpl
    #
    @55
    @93
    @71
    @55
    @70
    @10
    cQ
    @55
    @12
    @60
    @70
    @10
    wcel
    wph
    @12
    @52
    @32
    adantr
    #
    @75
    @8
    @48
    @3
    fnfvelrn
    syl2anc
    mpfind.cq
    syl6eleqr
    @55
    @36
    @49
    @71
    wph
    @36
    @52
    @38
    adantr
    #
    @73
    @48
    @0
    @3
    fvimacnvi
    syl2anc
    jca
    #
    @55
    @95
    @77
    @55
    @76
    @10
    cQ
    @55
    @12
    @61
    @76
    @10
    wcel
    @99
    @81
    @8
    @50
    @3
    fnfvelrn
    syl2anc
    mpfind.cq
    syl6eleqr
    @55
    @36
    @51
    @77
    @100
    @79
    @50
    @0
    @3
    fvimacnvi
    syl2anc
    jca
    #
    wph
    vf
    cv
    #
    cQ
    wcel
    #
    wta
    wa
    #
    vg
    cv
    #
    cQ
    wcel
    #
    wet
    wa
    #
    wa
    #
    wa
    #
    wze
    wi
    wph
    @94
    @96
    wa
    #
    wa
    #
    @97
    wi
    vf
    vg
    @70
    @76
    @48
    @3
    fvex
    #
    @50
    @3
    fvex
    #
    @103
    @70
    wceq
    #
    @106
    @76
    wceq
    #
    wa
    #
    @110
    @112
    wze
    @97
    @117
    @109
    @111
    wph
    @115
    @105
    @94
    @116
    @108
    @96
    @115
    @104
    @93
    wta
    @71
    @103
    @70
    cQ
    eleq1
    wta
    @103
    @0
    wcel
    @115
    @71
    wps
    wta
    vx
    @103
    vf
    vex
    mpfind.wc
    elab
    @103
    @70
    @0
    eleq1
    syl5bbr
    anbi12d
    @116
    @107
    @95
    wet
    @77
    @106
    @76
    cQ
    eleq1
    wet
    @106
    @0
    wcel
    @116
    @77
    wps
    wet
    vx
    @106
    vg
    vex
    mpfind.wd
    elab
    @106
    @76
    @0
    eleq1
    syl5bbr
    anbi12d
    bi2anan9
    anbi2d
    #
    wze
    @103
    @106
    @82
    co
    #
    @0
    wcel
    @117
    @97
    wps
    wze
    vx
    @119
    @103
    @106
    @82
    ovex
    mpfind.we
    elab
    @117
    @119
    @83
    @0
    @103
    @70
    @106
    @76
    @82
    oveq12
    eleq1d
    syl5bbr
    imbi12d
    mpfind.ad
    vtocl2
    syl12anc
    eqeltrd
    wph
    @54
    @56
    @58
    wa
    wb
    #
    @52
    wph
    @12
    @120
    @32
    @8
    @53
    @0
    @3
    elpreima
    syl
    adantr
    mpbir2and
    adantlr
    wph
    @52
    @48
    @50
    @41
    co
    #
    @37
    wcel
    #
    @33
    @55
    @122
    @121
    @8
    wcel
    #
    @121
    @3
    cfv
    #
    @0
    wcel
    #
    @55
    @59
    @60
    @61
    @123
    @69
    @75
    @81
    @8
    @7
    @41
    @48
    @50
    @29
    @46
    ringcl
    syl3anc
    @55
    @124
    @70
    @76
    c.x
    cof
    #
    co
    #
    @0
    @55
    @124
    @70
    @76
    @14
    cmulr
    cfv
    #
    co
    #
    @127
    @55
    @3
    @7
    cmgp
    cfv
    #
    @14
    cmgp
    cfv
    #
    cmhm
    co
    wcel
    #
    @60
    @61
    @124
    @129
    wceq
    wph
    @132
    @52
    wph
    @17
    @132
    @28
    @7
    @14
    @3
    @130
    @131
    @130
    eqid
    #
    @131
    eqid
    #
    rhmmhm
    syl
    adantr
    @75
    @81
    @8
    @41
    @128
    @130
    @131
    @3
    @48
    @50
    @8
    @7
    @130
    @133
    @29
    mgpbas
    @7
    @41
    @130
    @133
    @46
    mgpplusg
    @14
    @128
    @131
    @134
    @128
    eqid
    #
    mgpplusg
    mhmlin
    syl3anc
    @55
    @15
    cS
    @128
    c.x
    @70
    @76
    @13
    ccrg
    cvv
    @14
    @27
    @30
    @88
    @89
    @91
    @92
    mpfind.ct
    @135
    pwsmulrval
    eqtrd
    @55
    wph
    @94
    @96
    @127
    @0
    wcel
    #
    @98
    @101
    @102
    @110
    wsi
    wi
    @112
    @136
    wi
    vf
    vg
    @70
    @76
    @113
    @114
    @117
    @110
    @112
    wsi
    @136
    @118
    wsi
    @103
    @106
    @126
    co
    #
    @0
    wcel
    @117
    @136
    wps
    wsi
    vx
    @137
    @103
    @106
    @126
    ovex
    mpfind.wf
    elab
    @117
    @137
    @127
    @0
    @103
    @70
    @106
    @76
    @126
    oveq12
    eleq1d
    syl5bbr
    imbi12d
    mpfind.mu
    vtocl2
    syl12anc
    eqeltrd
    wph
    @122
    @123
    @125
    wa
    wb
    #
    @52
    wph
    @12
    @138
    @32
    @8
    @121
    @0
    @3
    elpreima
    syl
    adantr
    mpbir2and
    adantlr
    wph
    @48
    @42
    wcel
    #
    @48
    @39
    cfv
    #
    @37
    wcel
    #
    @33
    wph
    @139
    wa
    #
    @141
    @140
    @8
    wcel
    #
    @140
    @3
    cfv
    #
    @0
    wcel
    #
    @142
    @7
    csca
    cfv
    #
    cbs
    cfv
    #
    @8
    @48
    @39
    wph
    @147
    @8
    @39
    wf
    #
    @139
    wph
    @39
    @146
    @7
    crh
    co
    wcel
    #
    @148
    wph
    @7
    casa
    wcel
    #
    @149
    wph
    @18
    @64
    @150
    @63
    @67
    @7
    @6
    cI
    cvv
    @25
    mplassa
    syl2anc
    @39
    @146
    @7
    @47
    @146
    eqid
    asclrhm
    syl
    @147
    @8
    @146
    @7
    @39
    @147
    eqid
    @29
    rhmf
    syl
    adantr
    wph
    @139
    @48
    @147
    wcel
    wph
    @42
    @147
    @48
    wph
    @6
    @146
    cbs
    wph
    @7
    @6
    cI
    cvv
    ccrg
    @25
    @63
    @67
    mplsca
    fveq2d
    eleq2d
    biimpa
    ffvelrnd
    @142
    @144
    @13
    @48
    csn
    #
    cxp
    #
    @0
    @142
    @39
    cB
    @3
    cR
    cS
    @6
    cI
    cvv
    @7
    @48
    @24
    @25
    @26
    mpfind.cb
    @47
    wph
    @18
    @139
    @63
    adantr
    wph
    @19
    @139
    @65
    adantr
    wph
    @20
    @139
    @66
    adantr
    wph
    @48
    cR
    wcel
    #
    @139
    wph
    cR
    @42
    @48
    wph
    cR
    cB
    wss
    #
    cR
    @42
    wceq
    wph
    @20
    @154
    @66
    cR
    cB
    cS
    mpfind.cb
    subrgss
    syl
    cR
    cB
    @6
    cS
    @26
    mpfind.cb
    ressbas2
    syl
    eleq2d
    biimpar
    #
    evlssca
    wph
    @139
    @153
    @152
    @0
    wcel
    #
    @155
    wph
    @156
    vi
    cR
    wph
    wch
    vf
    cR
    wral
    @156
    vi
    cR
    wral
    wph
    wch
    vf
    cR
    mpfind.co
    ralrimiva
    wch
    @156
    vf
    vi
    cR
    wch
    @13
    @103
    csn
    #
    cxp
    #
    @0
    wcel
    @103
    @48
    wceq
    #
    @156
    wps
    wch
    vx
    @158
    @13
    @157
    cB
    cI
    cmap
    ovex
    #
    @103
    snex
    xpex
    mpfind.wa
    elab
    @159
    @158
    @152
    @0
    @159
    @157
    @151
    @13
    @103
    @48
    sneq
    xpeq2d
    eleq1d
    syl5bbr
    cbvralv
    sylib
    r19.21bi
    syldan
    eqeltrd
    wph
    @141
    @143
    @145
    wa
    wb
    #
    @139
    wph
    @12
    @161
    @32
    @8
    @140
    @0
    @3
    elpreima
    syl
    adantr
    mpbir2and
    adantlr
    wph
    @48
    cI
    wcel
    #
    @48
    @43
    cfv
    #
    @37
    wcel
    #
    @33
    wph
    @162
    wa
    #
    @164
    @163
    @8
    wcel
    #
    @163
    @3
    cfv
    #
    @0
    wcel
    #
    @165
    @8
    @7
    @6
    cI
    @43
    cvv
    @48
    @25
    @44
    @29
    wph
    @18
    @162
    @63
    adantr
    #
    wph
    @62
    @162
    @68
    adantr
    wph
    @162
    simpr
    #
    mvrcl
    @165
    @167
    vg
    @13
    @48
    @106
    cfv
    #
    cmpt
    #
    @0
    @165
    cB
    @3
    cR
    cS
    @6
    vg
    cI
    @43
    cvv
    @48
    @24
    @44
    @26
    mpfind.cb
    @169
    wph
    @19
    @162
    @65
    adantr
    wph
    @20
    @162
    @66
    adantr
    @170
    evlsvar
    wph
    @172
    @0
    wcel
    #
    vi
    cI
    wph
    vg
    @13
    @103
    @106
    cfv
    #
    cmpt
    #
    @0
    wcel
    #
    vf
    cI
    wral
    @173
    vi
    cI
    wral
    wph
    @176
    vf
    cI
    wph
    @103
    cI
    wcel
    wa
    wth
    @176
    mpfind.pr
    wps
    wth
    vx
    @175
    vg
    @13
    @174
    @160
    mptex
    mpfind.wb
    elab
    sylibr
    ralrimiva
    @176
    @173
    vf
    vi
    cI
    @159
    @175
    @172
    @0
    @159
    vg
    @13
    @174
    @171
    @103
    @48
    @106
    fveq2
    mpteq2dv
    eleq1d
    cbvralv
    sylib
    r19.21bi
    eqeltrd
    wph
    @164
    @166
    @168
    wa
    wb
    #
    @162
    wph
    @12
    @177
    @32
    @8
    @163
    @0
    @3
    elpreima
    syl
    adantr
    mpbir2and
    adantlr
    wph
    @33
    simpr
    wph
    @18
    @33
    @63
    adantr
    wph
    @64
    @33
    @67
    adantr
    mplind
    @2
    @0
    @3
    fvimacnvi
    syl2anc
    @4
    cA
    @0
    eleq1
    syl5ibcom
    rexlimdva
    mpd
    wph
    @22
    @1
    wrh
    wb
    mpfind.a
    wps
    wrh
    vx
    cA
    cQ
    mpfind.wg
    elabg
    syl
    mpbid
end
