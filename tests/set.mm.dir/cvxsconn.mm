include "cpconn.mm"
include "wcel.mm"
include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "cicc.mm"
include "co.mm"
include "csn.mm"
include "cxp.mm"
include "cphtpc.mm"
include "wbr.mm"
include "wi.mm"
include "cii.mm"
include "ccn.mm"
include "wral.mm"
include "csconn.mm"
include "cvxpconn.mm"
include "wa.mm"
include "cphtpy.mm"
include "c0.mm"
include "wne.mm"
include "simprl.mm"
include "cuni.mm"
include "ctopon.mm"
include "w3a.mm"
include "ctop.mm"
include "pconntop.mm"
include "syl.mm"
include "adantr.mm"
include "eqid.mm"
include "toptopon.mm"
include "sylib.mm"
include "wf.mm"
include "iiuni.mm"
include "cnf.mm"
include "0elunit.mm"
include "ffvelrn.mm"
include "sylancl.mm"
include "pcoptcl.mm"
include "syl2anc.mm"
include "simp1d.mm"
include "cmul.mm"
include "cmin.mm"
include "caddc.mm"
include "cmpt2.mm"
include "ctx.mm"
include "crest.mm"
include "iitopon.mm"
include "a1i.mm"
include "cc.mm"
include "dfii3.mm"
include "cnfldtopon.mm"
include "wss.mm"
include "cr.mm"
include "unitssre.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "cnmpt2nd.mm"
include "cnmpt2res.mm"
include "resttopon.mm"
include "sylancr.mm"
include "syl5eqel.mm"
include "toponuni.mm"
include "eleqtrrd.mm"
include "sseldd.mm"
include "cnmpt2c.mm"
include "mulcn.mm"
include "cnmpt22f.mm"
include "ax-1cn.mm"
include "subcn.mm"
include "cnmpt1st.mm"
include "cnfldtop.mm"
include "cnrest2r.mm"
include "ax-mp.mm"
include "oveq2i.mm"
include "syl6eleq.mm"
include "sseldi.mm"
include "cnmpt21f.mm"
include "addcn.mm"
include "crn.mm"
include "wb.mm"
include "ffvelrnd.mm"
include "3exp2.mm"
include "imp42.mm"
include "an32s.mm"
include "ralrimivva.mm"
include "ad2ant2rl.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "eleq1d.mm"
include "oveq2d.mm"
include "rspc2va.mm"
include "syl21anc.mm"
include "fmpt2.mm"
include "frn.mm"
include "cnrest2.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "syl6eleqr.mm"
include "simpr.mm"
include "weq.mm"
include "1m0e1.mm"
include "syl6eq.mm"
include "simpl.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "ovex.mm"
include "ovmpt2a.mm"
include "mul02d.mm"
include "toponunii.mm"
include "ffvelrnda.mm"
include "mulid2d.mm"
include "addid2d.mm"
include "3eqtrd.mm"
include "1elunit.mm"
include "1m1e0.mm"
include "addid1d.mm"
include "fvex.mm"
include "fvconst2.mm"
include "adantl.mm"
include "eqtr4d.mm"
include "pncan3.mm"
include "subcl.mm"
include "adddird.mm"
include "3eqtr3d.mm"
include "eqtrd.mm"
include "simplrr.mm"
include "isphtpy2d.mm"
include "ne0i.mm"
include "isphtpc.mm"
include "syl3anbrc.mm"
include "expr.mm"
include "ralrimiva.mm"
include "issconn.mm"
include "sylanbrc.mm"

theorem cvxsconn
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vt: setvar t
  let cS: class S
  let cJ: class J
  let cK: class K
  let vz: setvar z
  let vf: setvar f
  let vs: setvar s
  assume cvxpconn.1: |- ( ph -> S C_ CC )
  assume cvxpconn.2: |- ( ( ph /\ ( x e. S /\ y e. S /\ t e. ( 0 [,] 1 ) ) ) -> ( ( t x. x ) + ( ( 1 - t ) x. y ) ) e. S )
  assume cvxpconn.3: |- J = ( TopOpen ` CCfld )
  assume cvxpconn.4: |- K = ( J |`t S )

  disjoint J t
  disjoint t x
  disjoint t y
  disjoint K t
  disjoint x y
  disjoint K x
  disjoint K y
  disjoint ph t
  disjoint ph x
  disjoint ph y
  disjoint S t
  disjoint S x
  disjoint S y
  disjoint t z
  disjoint J z
  disjoint f s
  disjoint f t
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint K f
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint K s
  disjoint x z
  disjoint y z
  disjoint K z
  disjoint f ph
  disjoint ph s
  disjoint ph z
  disjoint S z
  assert |- ( ph -> K e. SConn )

  proof
    wph
    cK
    cpconn
    wcel
    #
    cc0
    vf
    cv
    #
    cfv
    #
    c1
    @1
    cfv
    #
    wceq
    #
    @1
    cc0
    c1
    cicc
    co
    #
    @2
    csn
    cxp
    #
    cK
    cphtpc
    cfv
    wbr
    #
    wi
    #
    vf
    cii
    cK
    ccn
    co
    #
    wral
    cK
    csconn
    wcel
    wph
    vx
    vy
    vt
    cS
    cJ
    cK
    cvxpconn.1
    cvxpconn.2
    cvxpconn.3
    cvxpconn.4
    cvxpconn
    #
    wph
    @8
    vf
    @9
    wph
    @1
    @9
    wcel
    #
    @4
    @7
    wph
    @11
    @4
    wa
    #
    wa
    #
    @11
    @6
    @9
    wcel
    #
    @1
    @6
    cK
    cphtpy
    cfv
    co
    #
    c0
    wne
    #
    @7
    wph
    @11
    @4
    simprl
    #
    @13
    @14
    cc0
    @6
    cfv
    @2
    wceq
    #
    c1
    @6
    cfv
    @2
    wceq
    #
    @13
    cK
    cK
    cuni
    #
    ctopon
    cfv
    wcel
    #
    @2
    @20
    wcel
    #
    @14
    @18
    @19
    w3a
    @13
    cK
    ctop
    wcel
    #
    @21
    wph
    @23
    @12
    wph
    @0
    @23
    @10
    cK
    pconntop
    syl
    adantr
    cK
    @20
    @20
    eqid
    #
    toptopon
    sylib
    @13
    @5
    @20
    @1
    wf
    #
    cc0
    @5
    wcel
    #
    @22
    @13
    @11
    @25
    @17
    @1
    cii
    cK
    @5
    @20
    iiuni
    @24
    cnf
    syl
    #
    0elunit
    @5
    @20
    cc0
    @1
    ffvelrn
    sylancl
    #
    @6
    cK
    @20
    @2
    @6
    eqid
    pcoptcl
    syl2anc
    simp1d
    #
    @13
    vz
    vt
    @5
    @5
    vt
    cv
    #
    @2
    cmul
    co
    #
    c1
    @30
    cmin
    co
    #
    vz
    cv
    #
    @1
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    cmpt2
    #
    @15
    wcel
    @16
    @13
    @1
    @6
    @37
    cK
    vs
    @17
    @29
    @13
    @37
    cii
    cii
    ctx
    co
    #
    cJ
    cS
    crest
    co
    #
    ccn
    co
    #
    @38
    cK
    ccn
    co
    @13
    @37
    @38
    cJ
    ccn
    co
    wcel
    #
    @37
    @40
    wcel
    #
    @13
    vz
    vt
    @31
    @35
    caddc
    cii
    cii
    cJ
    cJ
    cJ
    @5
    @5
    cii
    @5
    ctopon
    cfv
    wcel
    @13
    iitopon
    a1i
    #
    @43
    @13
    vz
    vt
    @30
    @2
    cmul
    cii
    cii
    cJ
    cJ
    cJ
    @5
    @5
    @43
    @43
    @13
    vz
    vt
    @30
    cJ
    cii
    cJ
    cJ
    cii
    @5
    cc
    @5
    cc
    cJ
    cvxpconn.3
    dfii3
    #
    cJ
    cc
    ctopon
    cfv
    wcel
    #
    @13
    cJ
    cvxpconn.3
    cnfldtopon
    #
    a1i
    #
    @5
    cc
    wss
    @13
    @5
    cr
    cc
    unitssre
    ax-resscn
    sstri
    #
    a1i
    #
    @44
    @47
    @49
    @13
    vz
    vt
    cJ
    cJ
    cc
    cc
    @47
    @47
    cnmpt2nd
    #
    cnmpt2res
    @13
    vz
    vt
    @2
    cii
    cii
    cJ
    @5
    @5
    cc
    @43
    @43
    @47
    @13
    cS
    cc
    @2
    wph
    cS
    cc
    wss
    #
    @12
    cvxpconn.1
    adantr
    #
    @13
    @2
    @20
    cS
    @28
    wph
    cS
    @20
    wceq
    #
    @12
    wph
    cK
    cS
    ctopon
    cfv
    #
    wcel
    @53
    wph
    cK
    @39
    @54
    cvxpconn.4
    wph
    @45
    @51
    @39
    @54
    wcel
    @46
    cvxpconn.1
    cS
    cJ
    cc
    resttopon
    sylancr
    syl5eqel
    cS
    cK
    toponuni
    syl
    adantr
    #
    eleqtrrd
    #
    sseldd
    #
    cnmpt2c
    cmul
    cJ
    cJ
    ctx
    co
    cJ
    ccn
    co
    #
    wcel
    @13
    cJ
    cvxpconn.3
    mulcn
    a1i
    #
    cnmpt22f
    @13
    vz
    vt
    @32
    @34
    cmul
    cii
    cii
    cJ
    cJ
    cJ
    @5
    @5
    @43
    @43
    @13
    vz
    vt
    @32
    cJ
    cii
    cJ
    cJ
    cii
    @5
    cc
    @5
    cc
    @44
    @47
    @49
    @44
    @47
    @49
    @13
    vz
    vt
    c1
    @30
    cmin
    cJ
    cJ
    cJ
    cJ
    cJ
    cc
    cc
    @47
    @47
    @13
    vz
    vt
    c1
    cJ
    cJ
    cJ
    cc
    cc
    cc
    @47
    @47
    @47
    c1
    cc
    wcel
    #
    @13
    ax-1cn
    a1i
    cnmpt2c
    @50
    cmin
    @58
    wcel
    @13
    cJ
    cvxpconn.3
    subcn
    a1i
    cnmpt22f
    cnmpt2res
    @13
    vz
    vt
    @33
    @1
    cii
    cii
    cii
    cJ
    @5
    @5
    @43
    @43
    @13
    vz
    vt
    cii
    cii
    @5
    @5
    @43
    @43
    cnmpt1st
    @13
    cii
    @39
    ccn
    co
    #
    cii
    cJ
    ccn
    co
    #
    @1
    cJ
    ctop
    wcel
    @61
    @62
    wss
    cJ
    cvxpconn.3
    cnfldtop
    cS
    cii
    cJ
    cnrest2r
    ax-mp
    @13
    @1
    @9
    @61
    @17
    cK
    @39
    cii
    ccn
    cvxpconn.4
    oveq2i
    syl6eleq
    sseldi
    #
    cnmpt21f
    @59
    cnmpt22f
    caddc
    @58
    wcel
    @13
    cJ
    cvxpconn.3
    addcn
    a1i
    cnmpt22f
    @13
    @45
    @37
    crn
    cS
    wss
    #
    @51
    @41
    @42
    wb
    @47
    @13
    @5
    @5
    cxp
    #
    cS
    @37
    wf
    #
    @64
    @13
    @36
    cS
    wcel
    #
    vt
    @5
    wral
    vz
    @5
    wral
    @66
    @13
    @67
    vz
    vt
    @5
    @5
    @13
    @33
    @5
    wcel
    #
    @30
    @5
    wcel
    #
    wa
    #
    wa
    #
    @2
    cS
    wcel
    #
    @34
    cS
    wcel
    @30
    vx
    cv
    #
    cmul
    co
    #
    @32
    vy
    cv
    #
    cmul
    co
    #
    caddc
    co
    #
    cS
    wcel
    #
    vy
    cS
    wral
    vx
    cS
    wral
    #
    @67
    @13
    @72
    @70
    @56
    adantr
    @71
    @34
    @20
    cS
    @71
    @5
    @20
    @33
    @1
    @13
    @25
    @70
    @27
    adantr
    @13
    @68
    @69
    simprl
    ffvelrnd
    @13
    @53
    @70
    @55
    adantr
    eleqtrrd
    wph
    @69
    @79
    @12
    @68
    wph
    @69
    wa
    @78
    vx
    vy
    cS
    cS
    wph
    @73
    cS
    wcel
    #
    @75
    cS
    wcel
    #
    wa
    @69
    @78
    wph
    @80
    @81
    @69
    @78
    wph
    @80
    @81
    @69
    @78
    cvxpconn.2
    3exp2
    imp42
    an32s
    ralrimivva
    ad2ant2rl
    @78
    @67
    @31
    @76
    caddc
    co
    #
    cS
    wcel
    vx
    vy
    @2
    @34
    cS
    cS
    @73
    @2
    wceq
    #
    @77
    @82
    cS
    @83
    @74
    @31
    @76
    caddc
    @73
    @2
    @30
    cmul
    oveq2
    oveq1d
    eleq1d
    @75
    @34
    wceq
    #
    @82
    @36
    cS
    @84
    @76
    @35
    @31
    caddc
    @75
    @34
    @32
    cmul
    oveq2
    oveq2d
    eleq1d
    rspc2va
    syl21anc
    ralrimivva
    vz
    vt
    @5
    @5
    @36
    cS
    @37
    @37
    eqid
    #
    fmpt2
    sylib
    @65
    cS
    @37
    frn
    syl
    @52
    cS
    @37
    @38
    cJ
    cc
    cnrest2
    syl3anc
    mpbid
    cK
    @39
    @38
    ccn
    cvxpconn.4
    oveq2i
    syl6eleqr
    @13
    vs
    cv
    #
    @5
    wcel
    #
    wa
    #
    @86
    cc0
    @37
    co
    #
    cc0
    @2
    cmul
    co
    #
    c1
    @86
    @1
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    cc0
    @91
    caddc
    co
    @91
    @88
    @87
    @26
    @89
    @93
    wceq
    @13
    @87
    simpr
    #
    0elunit
    vz
    vt
    @86
    cc0
    @5
    @5
    @36
    @93
    @37
    vz
    vs
    weq
    #
    @30
    cc0
    wceq
    #
    wa
    #
    @31
    @90
    @35
    @92
    caddc
    @97
    @30
    cc0
    @2
    cmul
    @95
    @96
    simpr
    #
    oveq1d
    @97
    @32
    c1
    @34
    @91
    cmul
    @97
    @32
    c1
    cc0
    cmin
    co
    c1
    @97
    @30
    cc0
    c1
    cmin
    @98
    oveq2d
    1m0e1
    syl6eq
    @97
    @33
    @86
    @1
    @95
    @96
    simpl
    fveq2d
    oveq12d
    oveq12d
    @85
    @90
    @92
    caddc
    ovex
    ovmpt2a
    sylancl
    @88
    @90
    cc0
    @92
    @91
    caddc
    @88
    @2
    @13
    @2
    cc
    wcel
    @87
    @57
    adantr
    #
    mul02d
    @88
    @91
    @13
    @5
    cc
    @86
    @1
    @13
    @1
    @62
    wcel
    @5
    cc
    @1
    wf
    @63
    @1
    cii
    cJ
    @5
    cc
    iiuni
    cc
    cJ
    @46
    toponunii
    cnf
    syl
    ffvelrnda
    #
    mulid2d
    oveq12d
    @88
    @91
    @100
    addid2d
    3eqtrd
    @88
    @86
    c1
    @37
    co
    #
    c1
    @2
    cmul
    co
    #
    cc0
    @91
    cmul
    co
    #
    caddc
    co
    #
    @2
    cc0
    caddc
    co
    #
    @86
    @6
    cfv
    #
    @88
    @87
    c1
    @5
    wcel
    #
    @101
    @104
    wceq
    @94
    1elunit
    vz
    vt
    @86
    c1
    @5
    @5
    @36
    @104
    @37
    @95
    @30
    c1
    wceq
    #
    wa
    #
    @31
    @102
    @35
    @103
    caddc
    @109
    @30
    c1
    @2
    cmul
    @95
    @108
    simpr
    #
    oveq1d
    @109
    @32
    cc0
    @34
    @91
    cmul
    @109
    @32
    c1
    c1
    cmin
    co
    cc0
    @109
    @30
    c1
    c1
    cmin
    @110
    oveq2d
    1m1e0
    syl6eq
    @109
    @33
    @86
    @1
    @95
    @108
    simpl
    fveq2d
    oveq12d
    oveq12d
    @85
    @102
    @103
    caddc
    ovex
    ovmpt2a
    sylancl
    @88
    @102
    @2
    @103
    cc0
    caddc
    @88
    @2
    @99
    mulid2d
    #
    @88
    @91
    @100
    mul02d
    oveq12d
    @88
    @105
    @2
    @106
    @88
    @2
    @99
    addid1d
    @87
    @106
    @2
    wceq
    @13
    @5
    @2
    @86
    cc0
    @1
    fvex
    fvconst2
    adantl
    eqtr4d
    3eqtrd
    @88
    cc0
    @86
    @37
    co
    #
    @86
    @2
    cmul
    co
    #
    c1
    @86
    cmin
    co
    #
    @2
    cmul
    co
    #
    caddc
    co
    #
    @2
    @88
    @26
    @87
    @112
    @116
    wceq
    0elunit
    @94
    vz
    vt
    cc0
    @86
    @5
    @5
    @36
    @116
    @37
    @33
    cc0
    wceq
    #
    vt
    vs
    weq
    #
    wa
    #
    @31
    @113
    @35
    @115
    caddc
    @119
    @30
    @86
    @2
    cmul
    @117
    @118
    simpr
    #
    oveq1d
    @119
    @32
    @114
    @34
    @2
    cmul
    @119
    @30
    @86
    c1
    cmin
    @120
    oveq2d
    @119
    @33
    cc0
    @1
    @117
    @118
    simpl
    fveq2d
    oveq12d
    oveq12d
    @85
    @113
    @115
    caddc
    ovex
    ovmpt2a
    sylancr
    @88
    @86
    @114
    caddc
    co
    #
    @2
    cmul
    co
    @102
    @116
    @2
    @88
    @121
    c1
    @2
    cmul
    @88
    @86
    cc
    wcel
    #
    @60
    @121
    c1
    wceq
    @88
    @5
    cc
    @86
    @48
    @94
    sseldi
    #
    ax-1cn
    @86
    c1
    pncan3
    sylancl
    oveq1d
    @88
    @86
    @114
    @2
    @123
    @88
    @60
    @122
    @114
    cc
    wcel
    ax-1cn
    @123
    c1
    @86
    subcl
    sylancr
    @99
    adddird
    @111
    3eqtr3d
    #
    eqtrd
    @88
    c1
    @86
    @37
    co
    #
    @113
    @114
    @3
    cmul
    co
    #
    caddc
    co
    #
    @3
    @88
    @107
    @87
    @125
    @127
    wceq
    1elunit
    @94
    vz
    vt
    c1
    @86
    @5
    @5
    @36
    @127
    @37
    @33
    c1
    wceq
    #
    @118
    wa
    #
    @31
    @113
    @35
    @126
    caddc
    @129
    @30
    @86
    @2
    cmul
    @128
    @118
    simpr
    #
    oveq1d
    @129
    @32
    @114
    @34
    @3
    cmul
    @129
    @30
    @86
    c1
    cmin
    @130
    oveq2d
    @129
    @33
    c1
    @1
    @128
    @118
    simpl
    fveq2d
    oveq12d
    oveq12d
    @85
    @113
    @126
    caddc
    ovex
    ovmpt2a
    sylancr
    @88
    @116
    @2
    @127
    @3
    @124
    @88
    @115
    @126
    @113
    caddc
    @88
    @2
    @3
    @114
    cmul
    wph
    @11
    @4
    @87
    simplrr
    #
    oveq2d
    oveq2d
    @131
    3eqtr3d
    eqtrd
    isphtpy2d
    @15
    @37
    ne0i
    syl
    @1
    @6
    cK
    isphtpc
    syl3anbrc
    expr
    ralrimiva
    vf
    cK
    issconn
    sylanbrc
end
