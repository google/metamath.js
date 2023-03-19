include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "cres.mm"
include "cima.mm"
include "wral.mm"
include "wrex.mm"
include "cvv.mm"
include "wcel.mm"
include "wfr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wf.mm"
include "wfun.mm"
include "ffun.mm"
include "vex.mm"
include "funimaex.mm"
include "3syl.mm"
include "wwe.mm"
include "wefr.mm"
include "syl.mm"
include "crn.mm"
include "imassrn.mm"
include "frn.mm"
include "syl5ss.mm"
include "cdm.mm"
include "cin.mm"
include "incom.mm"
include "wceq.mm"
include "fdm.mm"
include "sseqtr4d.mm"
include "df-ss.mm"
include "sylib.mm"
include "syl5eq.mm"
include "eqnetrd.mm"
include "imadisj.mm"
include "necon3bii.mm"
include "sylibr.mm"
include "fri.mm"
include "syl22anc.mm"
include "cfv.mm"
include "df-ima.mm"
include "rexeqi.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "fnssres.mm"
include "syl2anc.mm"
include "breq2.mm"
include "notbid.mm"
include "ralbidv.mm"
include "rexrn.mm"
include "syl5bb.mm"
include "wel.mm"
include "wa.mm"
include "raleqi.mm"
include "breq1.mm"
include "ralrn.mm"
include "adantr.mm"
include "resabs1d.mm"
include "ad2antrr.mm"
include "fveq1d.mm"
include "fvres.mm"
include "adantl.mm"
include "eqtrd.mm"
include "ad2antlr.mm"
include "breq12d.mm"
include "ralbidva.mm"
include "bitrd.mm"
include "rexbidva.mm"
include "csb.mm"
include "crab.mm"
include "inex1.mm"
include "a1i.mm"
include "sselda.mm"
include "fnwe2lem1.mm"
include "syldan.mm"
include "adantrr.mm"
include "inss2.mm"
include "simprl.mm"
include "eqidd.mm"
include "weq.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "elind.mm"
include "ne0i.mm"
include "wi.mm"
include "elin.mm"
include "anbi2i.mm"
include "bitri.mm"
include "imbi1i.mm"
include "impexp.mm"
include "ralbii2.mm"
include "simplrl.mm"
include "wo.mm"
include "simpr.mm"
include "simplrr.mm"
include "breq1d.mm"
include "rspcva.mm"
include "simprrr.mm"
include "breq2d.mm"
include "mtbird.mm"
include "ad3antrrr.mm"
include "simprr.mm"
include "simplr.mm"
include "eleq1.mm"
include "anbi12d.mm"
include "imbi12d.mm"
include "mp2and.mm"
include "eqtr2d.mm"
include "csbeq1d.mm"
include "breqd.mm"
include "mtbid.mm"
include "expr.mm"
include "imnan.mm"
include "ioran.mm"
include "fnwe2val.mm"
include "sylnibr.mm"
include "ralrimiva.mm"
include "rspcev.mm"
include "ex.mm"
include "syl5bi.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "rexlimdvaa.mm"
include "sylbid.mm"

theorem fnwe2lem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  assume fnwe2.su: |- ( z = ( F ` x ) -> S = U )
  assume fnwe2.t: |- T = { <. x , y >. | ( ( F ` x ) R ( F ` y ) \/ ( ( F ` x ) = ( F ` y ) /\ x U y ) ) }
  assume fnwe2.s: |- ( ( ph /\ x e. A ) -> U We { y e. A | ( F ` y ) = ( F ` x ) } )
  assume fnwe2.f: |- ( ph -> ( F |` A ) : A --> B )
  assume fnwe2.r: |- ( ph -> R We B )
  assume fnwe2lem2.a: |- ( ph -> a C_ A )
  assume fnwe2lem2.n0: |- ( ph -> a =/= (/) )

  disjoint b ph
  disjoint U y
  disjoint U z
  disjoint U a
  disjoint U b
  disjoint U c
  disjoint y z
  disjoint a y
  disjoint b y
  disjoint c y
  disjoint a z
  disjoint b z
  disjoint c z
  disjoint a b
  disjoint a c
  disjoint b c
  disjoint S x
  disjoint S y
  disjoint S a
  disjoint S b
  disjoint S c
  disjoint x y
  disjoint a x
  disjoint b x
  disjoint c x
  disjoint R x
  disjoint R y
  disjoint R a
  disjoint R b
  disjoint R c
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint c ph
  disjoint x z
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint T a
  disjoint T b
  disjoint T c
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint U d
  disjoint U e
  disjoint U f
  disjoint d y
  disjoint e y
  disjoint f y
  disjoint d z
  disjoint e z
  disjoint f z
  disjoint a d
  disjoint a e
  disjoint a f
  disjoint b d
  disjoint b e
  disjoint b f
  disjoint c d
  disjoint c e
  disjoint c f
  disjoint d e
  disjoint d f
  disjoint e f
  disjoint S d
  disjoint S e
  disjoint S f
  disjoint S g
  disjoint d x
  disjoint e x
  disjoint f x
  disjoint g x
  disjoint g y
  disjoint a g
  disjoint b g
  disjoint c g
  disjoint d g
  disjoint e g
  disjoint f g
  disjoint R d
  disjoint R e
  disjoint R f
  disjoint d ph
  disjoint e ph
  disjoint f ph
  disjoint g ph
  disjoint g z
  disjoint A d
  disjoint A e
  disjoint A f
  disjoint A g
  disjoint F d
  disjoint F e
  disjoint F f
  disjoint F g
  disjoint T d
  disjoint T e
  disjoint T f
  disjoint B d
  disjoint B e
  disjoint B f
  assert |- ( ph -> E. b e. a A. c e. a -. c T b )

  proof
    wph
    ve
    cv
    #
    vd
    cv
    #
    cR
    wbr
    #
    wn
    #
    ve
    cF
    cA
    cres
    #
    va
    cv
    #
    cima
    #
    wral
    #
    vd
    @6
    wrex
    #
    vc
    cv
    #
    vb
    cv
    #
    cT
    wbr
    #
    wn
    #
    vc
    @5
    wral
    #
    vb
    @5
    wrex
    #
    wph
    @6
    cvv
    wcel
    #
    cB
    cR
    wfr
    #
    @6
    cB
    wss
    @6
    c0
    wne
    #
    @8
    wph
    cA
    cB
    @4
    wf
    #
    @4
    wfun
    @15
    fnwe2.f
    cA
    cB
    @4
    ffun
    @4
    @5
    va
    vex
    #
    funimaex
    3syl
    wph
    cB
    cR
    wwe
    @16
    fnwe2.r
    cB
    cR
    wefr
    syl
    wph
    @6
    @4
    crn
    #
    cB
    @4
    @5
    imassrn
    wph
    @18
    @20
    cB
    wss
    fnwe2.f
    cA
    cB
    @4
    frn
    syl
    syl5ss
    wph
    @4
    cdm
    #
    @5
    cin
    #
    c0
    wne
    @17
    wph
    @22
    @5
    c0
    wph
    @22
    @5
    @21
    cin
    #
    @5
    @21
    @5
    incom
    wph
    @5
    @21
    wss
    @23
    @5
    wceq
    wph
    @5
    cA
    @21
    fnwe2lem2.a
    wph
    @18
    @21
    cA
    wceq
    fnwe2.f
    cA
    cB
    @4
    fdm
    syl
    sseqtr4d
    @5
    @21
    df-ss
    sylib
    syl5eq
    fnwe2lem2.n0
    eqnetrd
    @6
    c0
    @22
    c0
    @4
    @5
    imadisj
    necon3bii
    sylibr
    vd
    ve
    cB
    @6
    cvv
    cR
    fri
    syl22anc
    wph
    @8
    @1
    cF
    cfv
    #
    vf
    cv
    #
    cF
    cfv
    #
    cR
    wbr
    #
    wn
    #
    vd
    @5
    wral
    #
    vf
    @5
    wrex
    #
    @14
    wph
    @8
    @0
    @25
    @4
    @5
    cres
    #
    cfv
    #
    cR
    wbr
    #
    wn
    #
    ve
    @6
    wral
    #
    vf
    @5
    wrex
    #
    @30
    @8
    @7
    vd
    @31
    crn
    #
    wrex
    #
    wph
    @36
    @7
    vd
    @6
    @37
    @4
    @5
    df-ima
    #
    rexeqi
    wph
    @31
    @5
    wfn
    #
    @38
    @36
    wb
    wph
    @4
    cA
    wfn
    #
    @5
    cA
    wss
    #
    @40
    wph
    @18
    @41
    fnwe2.f
    cA
    cB
    @4
    ffn
    syl
    fnwe2lem2.a
    cA
    @5
    @4
    fnssres
    syl2anc
    #
    @7
    @35
    vd
    vf
    @5
    @31
    @1
    @32
    wceq
    #
    @3
    @34
    ve
    @6
    @44
    @2
    @33
    @1
    @32
    @0
    cR
    breq2
    notbid
    ralbidv
    rexrn
    syl
    syl5bb
    wph
    @35
    @29
    vf
    @5
    wph
    vf
    va
    wel
    #
    wa
    #
    @35
    @1
    @31
    cfv
    #
    @32
    cR
    wbr
    #
    wn
    #
    vd
    @5
    wral
    #
    @29
    wph
    @35
    @50
    wb
    @45
    @35
    @34
    ve
    @37
    wral
    #
    wph
    @50
    @34
    ve
    @6
    @37
    @39
    raleqi
    wph
    @40
    @51
    @50
    wb
    @43
    @34
    @49
    ve
    vd
    @5
    @31
    @0
    @47
    wceq
    @33
    @48
    @0
    @47
    @32
    cR
    breq1
    notbid
    ralrn
    syl
    syl5bb
    adantr
    @46
    @49
    @28
    vd
    @5
    @46
    vd
    va
    wel
    #
    wa
    #
    @48
    @27
    @53
    @47
    @24
    @32
    @26
    cR
    @53
    @47
    @1
    cF
    @5
    cres
    #
    cfv
    #
    @24
    @53
    @1
    @31
    @54
    wph
    @31
    @54
    wceq
    @45
    @52
    wph
    cF
    @5
    cA
    fnwe2lem2.a
    resabs1d
    ad2antrr
    #
    fveq1d
    @52
    @55
    @24
    wceq
    @46
    @1
    @5
    cF
    fvres
    adantl
    eqtrd
    @53
    @32
    @25
    @54
    cfv
    #
    @26
    @53
    @25
    @31
    @54
    @56
    fveq1d
    @45
    @57
    @26
    wceq
    wph
    @52
    @25
    @5
    cF
    fvres
    ad2antlr
    eqtrd
    breq12d
    notbid
    ralbidva
    bitrd
    rexbidva
    bitrd
    wph
    @29
    @14
    vf
    @5
    wph
    @45
    @29
    wa
    #
    wa
    #
    vg
    cv
    #
    @0
    vz
    @26
    cS
    csb
    #
    wbr
    #
    wn
    #
    vg
    @5
    vy
    cv
    #
    cF
    cfv
    #
    @26
    wceq
    #
    vy
    cA
    crab
    #
    cin
    #
    wral
    #
    ve
    @68
    wrex
    #
    @14
    @59
    @68
    cvv
    wcel
    #
    @67
    @61
    wfr
    #
    @68
    @67
    wss
    #
    @68
    c0
    wne
    #
    @70
    @71
    @59
    @5
    @67
    @19
    inex1
    a1i
    wph
    @45
    @72
    @29
    wph
    @45
    @25
    cA
    wcel
    #
    @72
    wph
    @5
    cA
    @25
    fnwe2lem2.a
    sselda
    #
    wph
    @75
    wa
    @67
    @61
    wwe
    @72
    wph
    vx
    vy
    vz
    cA
    cR
    cS
    cT
    cU
    cF
    vf
    fnwe2.su
    fnwe2.t
    fnwe2.s
    fnwe2lem1
    @67
    @61
    wefr
    syl
    syldan
    adantrr
    @73
    @59
    @5
    @67
    inss2
    a1i
    @59
    @25
    @68
    wcel
    @74
    @59
    @5
    @67
    @25
    wph
    @45
    @29
    simprl
    @59
    @75
    @26
    @26
    wceq
    #
    @25
    @67
    wcel
    wph
    @45
    @75
    @29
    @76
    adantrr
    @59
    @26
    eqidd
    @66
    @77
    vy
    @25
    cA
    vy
    vf
    weq
    @65
    @26
    @26
    @64
    @25
    cF
    fveq2
    eqeq1d
    elrab
    sylanbrc
    elind
    @68
    @25
    ne0i
    syl
    ve
    vg
    @67
    @68
    cvv
    @61
    fri
    syl22anc
    @59
    @69
    @14
    ve
    @68
    @0
    @68
    wcel
    #
    ve
    va
    wel
    #
    @0
    cA
    wcel
    #
    @0
    cF
    cfv
    #
    @26
    wceq
    #
    wa
    #
    wa
    #
    @59
    @69
    @14
    wi
    #
    @78
    @79
    @0
    @67
    wcel
    #
    wa
    @84
    @0
    @5
    @67
    elin
    @86
    @83
    @79
    @66
    @82
    vy
    @0
    cA
    vy
    ve
    weq
    @65
    @81
    @26
    @64
    @0
    cF
    fveq2
    eqeq1d
    elrab
    anbi2i
    bitri
    @59
    @84
    @85
    @69
    @60
    cA
    wcel
    #
    @60
    cF
    cfv
    #
    @26
    wceq
    #
    wa
    #
    @63
    wi
    #
    vg
    @5
    wral
    #
    @59
    @84
    wa
    #
    @14
    @63
    @91
    vg
    @68
    @5
    @60
    @68
    wcel
    #
    @63
    wi
    vg
    va
    wel
    #
    @90
    wa
    #
    @63
    wi
    @95
    @91
    wi
    @94
    @96
    @63
    @94
    @95
    @60
    @67
    wcel
    #
    wa
    @96
    @60
    @5
    @67
    elin
    @97
    @90
    @95
    @66
    @89
    vy
    @60
    cA
    vy
    vg
    weq
    @65
    @88
    @26
    @64
    @60
    cF
    fveq2
    eqeq1d
    elrab
    anbi2i
    bitri
    imbi1i
    @95
    @90
    @63
    impexp
    bitri
    ralbii2
    @93
    @92
    @14
    @93
    @92
    wa
    #
    @79
    @9
    @0
    cT
    wbr
    #
    wn
    #
    vc
    @5
    wral
    #
    @14
    @59
    @79
    @83
    @92
    simplrl
    @98
    @100
    vc
    @5
    @98
    vc
    va
    wel
    #
    wa
    #
    @9
    cF
    cfv
    #
    @81
    cR
    wbr
    #
    @104
    @81
    wceq
    #
    @9
    @0
    vz
    @104
    cS
    csb
    #
    wbr
    #
    wa
    #
    wo
    #
    @99
    @103
    @105
    wn
    @109
    wn
    #
    @110
    wn
    @103
    @105
    @104
    @26
    cR
    wbr
    #
    @103
    @102
    @29
    @112
    wn
    #
    @98
    @102
    simpr
    @93
    @29
    @92
    @102
    wph
    @45
    @29
    @84
    simplrr
    ad2antrr
    @28
    @113
    vd
    @9
    @5
    vd
    vc
    weq
    #
    @27
    @112
    @114
    @24
    @104
    @26
    cR
    @1
    @9
    cF
    fveq2
    breq1d
    notbid
    rspcva
    syl2anc
    @103
    @81
    @26
    @104
    cR
    @93
    @82
    @92
    @102
    @59
    @79
    @80
    @82
    simprrr
    #
    ad2antrr
    breq2d
    mtbird
    @103
    @106
    @108
    wn
    #
    wi
    @111
    @98
    @102
    @106
    @116
    @98
    @102
    @106
    wa
    #
    wa
    #
    @9
    @0
    @61
    wbr
    #
    @108
    @118
    @9
    cA
    wcel
    #
    @104
    @26
    wceq
    #
    @119
    wn
    #
    @98
    @102
    @120
    @106
    @98
    @5
    cA
    @9
    wph
    @42
    @58
    @84
    @92
    fnwe2lem2.a
    ad3antrrr
    sselda
    adantrr
    @118
    @104
    @81
    @26
    @98
    @102
    @106
    simprr
    #
    @93
    @82
    @92
    @117
    @115
    ad2antrr
    #
    eqtrd
    @118
    @102
    @92
    @120
    @121
    wa
    #
    @122
    wi
    #
    @98
    @102
    @106
    simprl
    @93
    @92
    @117
    simplr
    @91
    @126
    vg
    @9
    @5
    vg
    vc
    weq
    #
    @90
    @125
    @63
    @122
    @127
    @87
    @120
    @89
    @121
    @60
    @9
    cA
    eleq1
    @127
    @88
    @104
    @26
    @60
    @9
    cF
    fveq2
    eqeq1d
    anbi12d
    @127
    @62
    @119
    @60
    @9
    @0
    @61
    breq1
    notbid
    imbi12d
    rspcva
    syl2anc
    mp2and
    @118
    @61
    @107
    @9
    @0
    @118
    vz
    @26
    @104
    cS
    @118
    @104
    @81
    @26
    @123
    @124
    eqtr2d
    csbeq1d
    breqd
    mtbid
    expr
    @106
    @108
    imnan
    sylib
    @105
    @109
    ioran
    sylanbrc
    vx
    vy
    vz
    cR
    cS
    cT
    cU
    cF
    vc
    ve
    fnwe2.su
    fnwe2.t
    fnwe2val
    sylnibr
    ralrimiva
    @13
    @101
    vb
    @0
    @5
    vb
    ve
    weq
    #
    @12
    @100
    vc
    @5
    @128
    @11
    @99
    @10
    @0
    @9
    cT
    breq2
    notbid
    ralbidv
    rspcev
    syl2anc
    ex
    syl5bi
    ex
    syl5bi
    rexlimdv
    mpd
    rexlimdvaa
    sylbid
    mpd
end
