include "cixp.mm"
include "ccl.mm"
include "cfv.mm"
include "ccld.mm"
include "wcel.mm"
include "wss.mm"
include "cmpt.mm"
include "cpt.mm"
include "cv.mm"
include "wa.mm"
include "ctopon.mm"
include "ctop.mm"
include "topontop.mm"
include "syl.mm"
include "cuni.mm"
include "wceq.mm"
include "toponuni.mm"
include "sseqtrd.mm"
include "eqid.mm"
include "clscld.mm"
include "syl2anc.mm"
include "ptcldmpt.mm"
include "fveq2i.mm"
include "syl6eleqr.mm"
include "wral.mm"
include "sscls.mm"
include "ralrimiva.mm"
include "ss2ixp.mm"
include "clsss2.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "wi.mm"
include "wfn.mm"
include "cdif.mm"
include "cfn.mm"
include "wrex.mm"
include "w3a.mm"
include "wex.mm"
include "cab.mm"
include "vex.mm"
include "weq.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "exbidv.mm"
include "elab.mm"
include "wb.mm"
include "nffvmpt1.mm"
include "nfel2.mm"
include "nfv.mm"
include "fveq2.mm"
include "eleq12d.mm"
include "cbvral.mm"
include "simpr.mm"
include "fvmpt2.mm"
include "eleq2d.mm"
include "ralbidva.mm"
include "syl5bb.mm"
include "adantr.mm"
include "biimpa.mm"
include "ciun.mm"
include "wf.mm"
include "csb.mm"
include "wacn.mm"
include "ad2antrr.mm"
include "simpll.mm"
include "elixp.mm"
include "simprbi.mm"
include "ad2antlr.mm"
include "clsndisj.mm"
include "ex.mm"
include "3expia.mm"
include "ralimdva.mm"
include "sylc.mm"
include "simprlr.mm"
include "simprr.mm"
include "cbvixpv.mm"
include "syl6eleq.mm"
include "r19.26.mm"
include "sylanbrc.mm"
include "ralim.mm"
include "crab.mm"
include "rabn0.mm"
include "dfin5.mm"
include "inss2.mm"
include "ssiun2.mm"
include "syl5ss.mm"
include "sseqin2.mm"
include "sylib.mm"
include "syl5eqr.mm"
include "neeq1d.mm"
include "syl5bbr.mm"
include "ralbiia.mm"
include "sylibr.mm"
include "nfiu1.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nfin.mm"
include "nfrex.mm"
include "csbeq1a.mm"
include "ineq12d.mm"
include "rexbidv.mm"
include "eleq1.mm"
include "acni3.mm"
include "ffn.mm"
include "ne0i.mm"
include "ixpin.mm"
include "ineq1i.mm"
include "eqtr4i.mm"
include "neeq1i.mm"
include "3imtr3i.mm"
include "sylan2br.mm"
include "sylan.mm"
include "exlimiv.mm"
include "expr.mm"
include "syldan.mm"
include "3adantr3.mm"
include "eleq2.mm"
include "ineq1.mm"
include "imbi12d.mm"
include "syl5ibrcom.mm"
include "expimpd.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "ctg.mm"
include "fmptd.mm"
include "ptval.mm"
include "syl5eq.mm"
include "pttopon.mm"
include "ctb.mm"
include "ptbas.mm"
include "clsss3.mm"
include "sseqtr4d.mm"
include "sselda.mm"
include "elcls3.mm"
include "mpbird.mm"
include "ssrdv.mm"
include "eqssd.mm"

theorem ptclsg
  let wph: wff ph
  let cA: class A
  let cR: class R
  let cS: class S
  let vk: setvar k
  let cJ: class J
  let cV: class V
  let cX: class X
  let vf: setvar f
  let vg: setvar g
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vh: setvar h
  assume ptcls.2: |- J = ( Xt_ ` ( k e. A |-> R ) )
  assume ptcls.a: |- ( ph -> A e. V )
  assume ptcls.j: |- ( ( ph /\ k e. A ) -> R e. ( TopOn ` X ) )
  assume ptcls.c: |- ( ( ph /\ k e. A ) -> S C_ X )
  assume ptclsg.1: |- ( ph -> U_ k e. A S e. AC_ A )

  disjoint k ph
  disjoint A k
  disjoint f g
  disjoint f k
  disjoint f u
  disjoint f ph
  disjoint g k
  disjoint g u
  disjoint g ph
  disjoint k u
  disjoint ph u
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint R f
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint R g
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint R u
  disjoint x y
  disjoint x z
  disjoint R x
  disjoint y z
  disjoint R y
  disjoint R z
  disjoint f h
  disjoint S f
  disjoint g h
  disjoint S g
  disjoint h u
  disjoint h y
  disjoint h z
  disjoint S h
  disjoint S u
  disjoint S y
  disjoint S z
  disjoint V g
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint A f
  disjoint A g
  disjoint h k
  disjoint h x
  disjoint A h
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A u
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint J f
  assert |- ( ph -> ( ( cls ` J ) ` X_ k e. A S ) = X_ k e. A ( ( cls ` R ) ` S ) )

  proof
    wph
    vk
    cA
    cS
    cixp
    #
    cJ
    ccl
    cfv
    cfv
    #
    vk
    cA
    cS
    cR
    ccl
    cfv
    cfv
    #
    cixp
    #
    wph
    @3
    cJ
    ccld
    cfv
    #
    wcel
    @0
    @3
    wss
    #
    @1
    @3
    wss
    wph
    @3
    vk
    cA
    cR
    cmpt
    #
    cpt
    cfv
    #
    ccld
    cfv
    @4
    wph
    cA
    @2
    vk
    cR
    cV
    ptcls.a
    wph
    vk
    cv
    #
    cA
    wcel
    #
    wa
    #
    cR
    cX
    ctopon
    cfv
    #
    wcel
    #
    cR
    ctop
    wcel
    #
    ptcls.j
    cX
    cR
    topontop
    syl
    #
    @10
    @13
    cS
    cR
    cuni
    #
    wss
    #
    @2
    cR
    ccld
    cfv
    wcel
    @14
    @10
    cS
    cX
    @15
    ptcls.c
    @10
    @12
    cX
    @15
    wceq
    ptcls.j
    cX
    cR
    toponuni
    syl
    #
    sseqtrd
    #
    cS
    cR
    @15
    @15
    eqid
    #
    clscld
    syl2anc
    ptcldmpt
    cJ
    @7
    ccld
    ptcls.2
    fveq2i
    syl6eleqr
    wph
    cS
    @2
    wss
    #
    vk
    cA
    wral
    @5
    wph
    @20
    vk
    cA
    @10
    @13
    @16
    @20
    @14
    @18
    cS
    cR
    @15
    @19
    sscls
    syl2anc
    ralrimiva
    vk
    cA
    cS
    @2
    ss2ixp
    syl
    @3
    @0
    cJ
    cJ
    cuni
    #
    @21
    eqid
    clsss2
    syl2anc
    wph
    vf
    @3
    @1
    wph
    vf
    cv
    #
    @3
    wcel
    #
    @22
    @1
    wcel
    #
    wph
    @23
    wa
    #
    @24
    @22
    vu
    cv
    #
    wcel
    #
    @26
    @0
    cin
    #
    c0
    wne
    #
    wi
    #
    vu
    vg
    cv
    #
    cA
    wfn
    #
    vy
    cv
    #
    @31
    cfv
    #
    @33
    @6
    cfv
    #
    wcel
    #
    vy
    cA
    wral
    #
    @34
    @35
    cuni
    wceq
    vy
    cA
    vz
    cv
    #
    cdif
    wral
    vz
    cfn
    wrex
    #
    w3a
    #
    vx
    cv
    #
    vy
    cA
    @34
    cixp
    #
    wceq
    #
    wa
    #
    vg
    wex
    #
    vx
    cab
    #
    wral
    @25
    @30
    vu
    @46
    @26
    @46
    wcel
    @40
    @26
    @42
    wceq
    #
    wa
    #
    vg
    wex
    #
    @25
    @30
    @45
    @49
    vx
    @26
    vu
    vex
    vx
    vu
    weq
    #
    @44
    @48
    vg
    @50
    @43
    @47
    @40
    @41
    @26
    @42
    eqeq1
    anbi2d
    exbidv
    elab
    @25
    @48
    @30
    vg
    @25
    @40
    @47
    @30
    @25
    @40
    wa
    @30
    @47
    @22
    @42
    wcel
    #
    @42
    @0
    cin
    #
    c0
    wne
    #
    wi
    #
    @25
    @32
    @37
    @54
    @39
    @25
    @32
    @37
    wa
    #
    @32
    @8
    @31
    cfv
    #
    cR
    wcel
    #
    vk
    cA
    wral
    #
    wa
    #
    @54
    @25
    @55
    @59
    wph
    @55
    @59
    wb
    @23
    wph
    @37
    @58
    @32
    @37
    @56
    @8
    @6
    cfv
    #
    wcel
    #
    vk
    cA
    wral
    wph
    @58
    @36
    @61
    vy
    vk
    cA
    vk
    @34
    @35
    vk
    cA
    cR
    @33
    nffvmpt1
    nfel2
    @61
    vy
    nfv
    vy
    vk
    weq
    @34
    @56
    @35
    @60
    @33
    @8
    @31
    fveq2
    #
    @33
    @8
    @6
    fveq2
    eleq12d
    cbvral
    wph
    @61
    @57
    vk
    cA
    @10
    @60
    cR
    @56
    @10
    @9
    @12
    @60
    cR
    wceq
    wph
    @9
    simpr
    ptcls.j
    vk
    cA
    cR
    @11
    @6
    @6
    eqid
    #
    fvmpt2
    syl2anc
    eleq2d
    ralbidva
    syl5bb
    anbi2d
    adantr
    biimpa
    @25
    @59
    @51
    @53
    @25
    @59
    @51
    wa
    #
    wa
    #
    cA
    vk
    cA
    cS
    ciun
    #
    vh
    cv
    #
    wf
    #
    @33
    @67
    cfv
    #
    @34
    vk
    @33
    cS
    csb
    #
    cin
    #
    wcel
    #
    vy
    cA
    wral
    #
    wa
    #
    vh
    wex
    #
    @53
    @65
    @66
    cA
    wacn
    wcel
    #
    @38
    @71
    wcel
    #
    vz
    @66
    wrex
    #
    vy
    cA
    wral
    #
    @75
    wph
    @76
    @23
    @64
    ptclsg.1
    ad2antrr
    @65
    @38
    @56
    cS
    cin
    #
    wcel
    #
    vz
    @66
    wrex
    #
    vk
    cA
    wral
    #
    @79
    @65
    @80
    c0
    wne
    #
    vk
    cA
    wral
    #
    @83
    @65
    @57
    @8
    @22
    cfv
    #
    @56
    wcel
    #
    wa
    #
    @84
    wi
    #
    vk
    cA
    wral
    #
    @88
    vk
    cA
    wral
    #
    @85
    @65
    wph
    @86
    @2
    wcel
    #
    vk
    cA
    wral
    #
    @90
    wph
    @23
    @64
    simpll
    @23
    @93
    wph
    @64
    @23
    @22
    cA
    wfn
    #
    @93
    vk
    cA
    @2
    @22
    vf
    vex
    #
    elixp
    simprbi
    ad2antlr
    wph
    @92
    @89
    vk
    cA
    @10
    @13
    @16
    @92
    @89
    wi
    @14
    @18
    @13
    @16
    @92
    @89
    @13
    @16
    @92
    w3a
    @88
    @84
    @86
    cS
    @56
    cR
    @15
    @19
    clsndisj
    ex
    3expia
    syl2anc
    ralimdva
    sylc
    @65
    @58
    @87
    vk
    cA
    wral
    #
    @91
    @25
    @32
    @58
    @51
    simprlr
    @65
    @22
    vk
    cA
    @56
    cixp
    #
    wcel
    #
    @96
    @65
    @22
    @42
    @97
    @25
    @59
    @51
    simprr
    vy
    vk
    cA
    @34
    @56
    @62
    cbvixpv
    #
    syl6eleq
    @98
    @94
    @96
    vk
    cA
    @56
    @22
    @95
    elixp
    simprbi
    syl
    @57
    @87
    vk
    cA
    r19.26
    sylanbrc
    @88
    @84
    vk
    cA
    ralim
    sylc
    @82
    @84
    vk
    cA
    @82
    @81
    vz
    @66
    crab
    #
    c0
    wne
    @9
    @84
    @81
    vz
    @66
    rabn0
    @9
    @100
    @80
    c0
    @9
    @100
    @66
    @80
    cin
    #
    @80
    vz
    @66
    @80
    dfin5
    @9
    @80
    @66
    wss
    @101
    @80
    wceq
    @9
    @80
    cS
    @66
    @56
    cS
    inss2
    vk
    cA
    cS
    ssiun2
    syl5ss
    @80
    @66
    sseqin2
    sylib
    syl5eqr
    neeq1d
    syl5bbr
    ralbiia
    sylibr
    @82
    @78
    vk
    vy
    cA
    @82
    vy
    nfv
    @77
    vk
    vz
    @66
    vk
    cA
    cS
    nfiu1
    vk
    @38
    @71
    vk
    @34
    @70
    vk
    @34
    nfcv
    vk
    @33
    cS
    nfcsb1v
    nfin
    #
    nfel2
    nfrex
    vk
    vy
    weq
    #
    @81
    @77
    vz
    @66
    @103
    @80
    @71
    @38
    @103
    @56
    @34
    cS
    @70
    @8
    @33
    @31
    fveq2
    vk
    @33
    cS
    csbeq1a
    ineq12d
    #
    eleq2d
    rexbidv
    cbvral
    sylib
    @77
    @72
    vy
    vz
    cA
    vh
    @66
    @38
    @69
    @71
    eleq1
    acni3
    syl2anc
    @74
    @53
    vh
    @68
    @67
    cA
    wfn
    #
    @73
    @53
    cA
    @66
    @67
    ffn
    @73
    @105
    @8
    @67
    cfv
    #
    @80
    wcel
    #
    vk
    cA
    wral
    #
    @53
    @107
    @72
    vk
    vy
    cA
    @107
    vy
    nfv
    vk
    @69
    @71
    @102
    nfel2
    @103
    @106
    @69
    @80
    @71
    @8
    @33
    @67
    fveq2
    @104
    eleq12d
    cbvral
    @67
    vk
    cA
    @80
    cixp
    #
    wcel
    @109
    c0
    wne
    @105
    @108
    wa
    @53
    @109
    @67
    ne0i
    vk
    cA
    @80
    @67
    vh
    vex
    elixp
    @109
    @52
    c0
    @109
    @97
    @0
    cin
    @52
    vk
    cA
    @56
    cS
    ixpin
    @42
    @97
    @0
    @99
    ineq1i
    eqtr4i
    neeq1i
    3imtr3i
    sylan2br
    sylan
    exlimiv
    syl
    expr
    syldan
    3adantr3
    @47
    @27
    @51
    @29
    @53
    @26
    @42
    @22
    eleq2
    @47
    @28
    @52
    c0
    @26
    @42
    @0
    ineq1
    neeq1d
    imbi12d
    syl5ibrcom
    expimpd
    exlimdv
    syl5bi
    ralrimiv
    @25
    vu
    @46
    @22
    @0
    cJ
    vk
    cA
    cX
    cixp
    #
    wph
    cJ
    @46
    ctg
    cfv
    #
    wceq
    @23
    wph
    cJ
    @7
    @111
    ptcls.2
    wph
    cA
    cV
    wcel
    #
    @6
    cA
    wfn
    #
    @7
    @111
    wceq
    ptcls.a
    wph
    cA
    ctop
    @6
    wf
    #
    @113
    wph
    vk
    cA
    cR
    ctop
    @6
    @14
    @63
    fmptd
    #
    cA
    ctop
    @6
    ffn
    syl
    vx
    vy
    vz
    cA
    @46
    vg
    @6
    cV
    @46
    eqid
    #
    ptval
    syl2anc
    syl5eq
    adantr
    wph
    @110
    @21
    wceq
    #
    @23
    wph
    cJ
    @110
    ctopon
    cfv
    wcel
    #
    @117
    wph
    @112
    @12
    vk
    cA
    wral
    @118
    ptcls.a
    wph
    @12
    vk
    cA
    ptcls.j
    ralrimiva
    vk
    cA
    cX
    cJ
    cR
    cV
    ptcls.2
    pttopon
    syl2anc
    @110
    cJ
    toponuni
    syl
    adantr
    wph
    @46
    ctb
    wcel
    #
    @23
    wph
    @112
    @114
    @119
    ptcls.a
    @115
    vx
    vy
    vz
    cA
    @46
    vg
    @6
    cV
    @116
    ptbas
    syl2anc
    adantr
    wph
    @0
    @110
    wss
    #
    @23
    wph
    cS
    cX
    wss
    #
    vk
    cA
    wral
    @120
    wph
    @121
    vk
    cA
    ptcls.c
    ralrimiva
    vk
    cA
    cS
    cX
    ss2ixp
    syl
    adantr
    wph
    @3
    @110
    @22
    wph
    @2
    cX
    wss
    #
    vk
    cA
    wral
    @3
    @110
    wss
    wph
    @122
    vk
    cA
    @10
    @2
    @15
    cX
    @10
    @13
    @16
    @2
    @15
    wss
    @14
    @18
    cS
    cR
    @15
    @19
    clsss3
    syl2anc
    @17
    sseqtr4d
    ralrimiva
    vk
    cA
    @2
    cX
    ss2ixp
    syl
    sselda
    elcls3
    mpbird
    ex
    ssrdv
    eqssd
end
