include "cmnd.mm"
include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "ccom.mm"
include "cmpt.mm"
include "wf.mm"
include "cplusg.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "c0g.mm"
include "w3a.mm"
include "cmhm.mm"
include "mhmrcl1.mm"
include "syl.mm"
include "pwsmnd.mm"
include "syl2anc.mm"
include "mhmrcl2.mm"
include "jca.mm"
include "eqid.mm"
include "mhmf.mm"
include "adantr.mm"
include "simpr.mm"
include "pwselbas.mm"
include "fco.mm"
include "wb.mm"
include "pwselbasb.mm"
include "mpbird.mm"
include "fmptd.mm"
include "cof.mm"
include "simprl.mm"
include "ffvelrnda.mm"
include "simprr.mm"
include "mhmlin.mm"
include "syl3anc.mm"
include "mpteq2dva.mm"
include "cvv.mm"
include "fvexd.mm"
include "feqmptd.mm"
include "fveq2.mm"
include "fmptco.mm"
include "offval2.mm"
include "eqtr4d.mm"
include "mndcl.mm"
include "pwsplusgval.mm"
include "eqtrd.mm"
include "3eqtr4d.mm"
include "3expb.mm"
include "sylan.mm"
include "coexg.mm"
include "coeq2.mm"
include "fvmptg.mm"
include "oveq12d.mm"
include "ralrimivva.mm"
include "csn.mm"
include "cxp.mm"
include "mndidcl.mm"
include "wfn.mm"
include "ffn.mm"
include "fcoconst.mm"
include "pws0g.mm"
include "coeq2d.mm"
include "mhm0.mm"
include "sneqd.mm"
include "xpeq2d.mm"
include "3eqtr3d.mm"
include "3eqtrd.mm"
include "3jca.mm"
include "ismhm.mm"
include "sylanbrc.mm"

theorem pwsco2mhm
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let vg: setvar g
  let cF: class F
  let cV: class V
  let cY: class Y
  let cZ: class Z
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume pwsco2mhm.y: |- Y = ( R ^s A )
  assume pwsco2mhm.z: |- Z = ( S ^s A )
  assume pwsco2mhm.b: |- B = ( Base ` Y )
  assume pwsco2mhm.a: |- ( ph -> A e. V )
  assume pwsco2mhm.f: |- ( ph -> F e. ( R MndHom S ) )

  disjoint B g
  disjoint F g
  disjoint Y g
  disjoint Z g
  disjoint g ph
  disjoint A w
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint w x
  disjoint w y
  disjoint B w
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint g z
  disjoint w z
  disjoint F w
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint Y x
  disjoint Y y
  disjoint Z x
  disjoint Z y
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint R w
  disjoint R z
  disjoint S w
  assert |- ( ph -> ( g e. B |-> ( F o. g ) ) e. ( Y MndHom Z ) )

  proof
    wph
    cY
    cmnd
    wcel
    #
    cZ
    cmnd
    wcel
    #
    wa
    cB
    cZ
    cbs
    cfv
    #
    vg
    cB
    cF
    vg
    cv
    #
    ccom
    #
    cmpt
    #
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    cY
    cplusg
    cfv
    #
    co
    #
    @5
    cfv
    #
    @7
    @5
    cfv
    #
    @8
    @5
    cfv
    #
    cZ
    cplusg
    cfv
    #
    co
    #
    wceq
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    cY
    c0g
    cfv
    #
    @5
    cfv
    #
    cZ
    c0g
    cfv
    #
    wceq
    #
    w3a
    @5
    cY
    cZ
    cmhm
    co
    wcel
    wph
    @0
    @1
    wph
    cR
    cmnd
    wcel
    #
    cA
    cV
    wcel
    #
    @0
    wph
    cF
    cR
    cS
    cmhm
    co
    #
    wcel
    #
    @22
    pwsco2mhm.f
    cR
    cS
    cF
    mhmrcl1
    #
    syl
    #
    pwsco2mhm.a
    cR
    cA
    cV
    cY
    pwsco2mhm.y
    pwsmnd
    syl2anc
    #
    wph
    cS
    cmnd
    wcel
    #
    @23
    @1
    wph
    @25
    @29
    pwsco2mhm.f
    cR
    cS
    cF
    mhmrcl2
    #
    syl
    #
    pwsco2mhm.a
    cS
    cA
    cV
    cZ
    pwsco2mhm.z
    pwsmnd
    syl2anc
    jca
    wph
    @6
    @17
    @21
    wph
    vg
    cB
    @4
    @2
    @5
    wph
    @3
    cB
    wcel
    #
    wa
    #
    @4
    @2
    wcel
    #
    cA
    cS
    cbs
    cfv
    #
    @4
    wf
    #
    @33
    cR
    cbs
    cfv
    #
    @35
    cF
    wf
    #
    cA
    @37
    @3
    wf
    @36
    wph
    @38
    @32
    wph
    @25
    @38
    pwsco2mhm.f
    @37
    @35
    cR
    cS
    cF
    @37
    eqid
    #
    @35
    eqid
    #
    mhmf
    #
    syl
    #
    adantr
    @33
    @37
    cR
    cA
    cB
    cmnd
    @3
    cY
    cV
    pwsco2mhm.y
    @39
    pwsco2mhm.b
    wph
    @22
    @32
    @27
    adantr
    wph
    @23
    @32
    pwsco2mhm.a
    adantr
    #
    wph
    @32
    simpr
    pwselbas
    cA
    @37
    @35
    cF
    @3
    fco
    syl2anc
    @33
    @29
    @23
    @34
    @36
    wb
    wph
    @29
    @32
    @31
    adantr
    @43
    @35
    cS
    cA
    @2
    cmnd
    @4
    cZ
    cV
    pwsco2mhm.z
    @40
    @2
    eqid
    #
    pwselbasb
    syl2anc
    mpbird
    @5
    eqid
    #
    fmptd
    wph
    @16
    vx
    vy
    cB
    cB
    wph
    @7
    cB
    wcel
    #
    @8
    cB
    wcel
    #
    wa
    #
    wa
    #
    cF
    @10
    ccom
    #
    cF
    @7
    ccom
    #
    cF
    @8
    ccom
    #
    @14
    co
    #
    @11
    @15
    @49
    vw
    cA
    vw
    cv
    #
    @7
    cfv
    #
    @54
    @8
    cfv
    #
    cR
    cplusg
    cfv
    #
    co
    #
    cF
    cfv
    #
    cmpt
    #
    @51
    @52
    cS
    cplusg
    cfv
    #
    cof
    co
    #
    @50
    @53
    @49
    @60
    vw
    cA
    @55
    cF
    cfv
    #
    @56
    cF
    cfv
    #
    @61
    co
    #
    cmpt
    @62
    @49
    vw
    cA
    @59
    @65
    @49
    @54
    cA
    wcel
    #
    wa
    #
    @25
    @55
    @37
    wcel
    #
    @56
    @37
    wcel
    #
    @59
    @65
    wceq
    @49
    @25
    @66
    wph
    @25
    @48
    pwsco2mhm.f
    adantr
    #
    adantr
    @49
    cA
    @37
    @54
    @7
    @49
    @37
    cR
    cA
    cB
    cmnd
    @7
    cY
    cV
    pwsco2mhm.y
    @39
    pwsco2mhm.b
    @49
    @25
    @22
    @70
    @26
    syl
    #
    wph
    @23
    @48
    pwsco2mhm.a
    adantr
    #
    wph
    @46
    @47
    simprl
    #
    pwselbas
    #
    ffvelrnda
    #
    @49
    cA
    @37
    @54
    @8
    @49
    @37
    cR
    cA
    cB
    cmnd
    @8
    cY
    cV
    pwsco2mhm.y
    @39
    pwsco2mhm.b
    @71
    @72
    wph
    @46
    @47
    simprr
    #
    pwselbas
    #
    ffvelrnda
    #
    @37
    @57
    @61
    cR
    cS
    cF
    @55
    @56
    @39
    @57
    eqid
    #
    @61
    eqid
    #
    mhmlin
    syl3anc
    mpteq2dva
    @49
    vw
    cA
    @63
    @64
    @61
    @51
    @52
    cV
    cvv
    cvv
    @72
    @67
    @55
    cF
    fvexd
    @67
    @56
    cF
    fvexd
    @49
    vw
    vz
    cA
    @37
    @55
    vz
    cv
    #
    cF
    cfv
    #
    @63
    @7
    cF
    @75
    @49
    vw
    cA
    @37
    @7
    @74
    feqmptd
    #
    @49
    vz
    @37
    @35
    cF
    @49
    @25
    @38
    @70
    @41
    syl
    #
    feqmptd
    #
    @81
    @55
    cF
    fveq2
    fmptco
    @49
    vw
    vz
    cA
    @37
    @56
    @82
    @64
    @8
    cF
    @78
    @49
    vw
    cA
    @37
    @8
    @77
    feqmptd
    #
    @85
    @81
    @56
    cF
    fveq2
    fmptco
    offval2
    eqtr4d
    @49
    vw
    vz
    cA
    @37
    @58
    @82
    @59
    @10
    cF
    @67
    @22
    @68
    @69
    @58
    @37
    wcel
    @49
    @22
    @66
    @71
    adantr
    @75
    @78
    @37
    @57
    cR
    @55
    @56
    @39
    @79
    mndcl
    syl3anc
    @49
    @10
    @7
    @8
    @57
    cof
    co
    vw
    cA
    @58
    cmpt
    @49
    cB
    @57
    @9
    cR
    @7
    @8
    cA
    cmnd
    cV
    cY
    pwsco2mhm.y
    pwsco2mhm.b
    @71
    @72
    @73
    @76
    @79
    @9
    eqid
    #
    pwsplusgval
    @49
    vw
    cA
    @55
    @56
    @57
    @7
    @8
    cV
    cvv
    cvv
    @72
    @67
    @54
    @7
    fvexd
    @67
    @54
    @8
    fvexd
    @83
    @86
    offval2
    eqtrd
    @85
    @81
    @58
    cF
    fveq2
    fmptco
    @49
    @2
    @61
    @14
    cS
    @51
    @52
    cA
    cmnd
    cV
    cZ
    pwsco2mhm.z
    @44
    @49
    @25
    @29
    @70
    @30
    syl
    #
    @72
    @49
    @51
    @2
    wcel
    #
    cA
    @35
    @51
    wf
    #
    @49
    @38
    cA
    @37
    @7
    wf
    @90
    @84
    @74
    cA
    @37
    @35
    cF
    @7
    fco
    syl2anc
    @49
    @29
    @23
    @89
    @90
    wb
    @88
    @72
    @35
    cS
    cA
    @2
    cmnd
    @51
    cZ
    cV
    pwsco2mhm.z
    @40
    @44
    pwselbasb
    syl2anc
    mpbird
    #
    @49
    @52
    @2
    wcel
    #
    cA
    @35
    @52
    wf
    #
    @49
    @38
    cA
    @37
    @8
    wf
    @93
    @84
    @77
    cA
    @37
    @35
    cF
    @8
    fco
    syl2anc
    @49
    @29
    @23
    @92
    @93
    wb
    @88
    @72
    @35
    cS
    cA
    @2
    cmnd
    @52
    cZ
    cV
    pwsco2mhm.z
    @40
    @44
    pwselbasb
    syl2anc
    mpbird
    #
    @80
    @14
    eqid
    #
    pwsplusgval
    3eqtr4d
    @49
    @10
    cB
    wcel
    #
    @50
    cvv
    wcel
    #
    @11
    @50
    wceq
    wph
    @0
    @48
    @96
    @28
    @0
    @46
    @47
    @96
    cB
    @9
    cY
    @7
    @8
    pwsco2mhm.b
    @87
    mndcl
    3expb
    sylan
    #
    @49
    @25
    @96
    @97
    @70
    @98
    cF
    @10
    @24
    cB
    coexg
    syl2anc
    vg
    @10
    @4
    @50
    cB
    cvv
    @5
    @3
    @10
    cF
    coeq2
    @45
    fvmptg
    syl2anc
    @49
    @12
    @51
    @13
    @52
    @14
    @49
    @46
    @89
    @12
    @51
    wceq
    @73
    @91
    vg
    @7
    @4
    @51
    cB
    @2
    @5
    @3
    @7
    cF
    coeq2
    @45
    fvmptg
    syl2anc
    @49
    @47
    @92
    @13
    @52
    wceq
    @76
    @94
    vg
    @8
    @4
    @52
    cB
    @2
    @5
    @3
    @8
    cF
    coeq2
    @45
    fvmptg
    syl2anc
    oveq12d
    3eqtr4d
    ralrimivva
    wph
    @19
    cF
    @18
    ccom
    #
    cA
    cS
    c0g
    cfv
    #
    csn
    #
    cxp
    #
    @20
    wph
    @18
    cB
    wcel
    #
    @99
    cvv
    wcel
    #
    @19
    @99
    wceq
    wph
    @0
    @103
    @28
    cB
    cY
    @18
    pwsco2mhm.b
    @18
    eqid
    #
    mndidcl
    syl
    #
    wph
    @25
    @103
    @104
    pwsco2mhm.f
    @106
    cF
    @18
    @24
    cB
    coexg
    syl2anc
    vg
    @18
    @4
    @99
    cB
    cvv
    @5
    @3
    @18
    cF
    coeq2
    @45
    fvmptg
    syl2anc
    wph
    cF
    cA
    cR
    c0g
    cfv
    #
    csn
    cxp
    #
    ccom
    #
    cA
    @107
    cF
    cfv
    #
    csn
    #
    cxp
    #
    @99
    @102
    wph
    cF
    @37
    wfn
    #
    @107
    @37
    wcel
    #
    @109
    @112
    wceq
    wph
    @38
    @113
    @42
    @37
    @35
    cF
    ffn
    syl
    wph
    @22
    @114
    @27
    @37
    cR
    @107
    @39
    @107
    eqid
    #
    mndidcl
    syl
    cF
    cA
    @37
    @107
    fcoconst
    syl2anc
    wph
    @108
    @18
    cF
    wph
    @22
    @23
    @108
    @18
    wceq
    @27
    pwsco2mhm.a
    cR
    cA
    cV
    cY
    @107
    pwsco2mhm.y
    @115
    pws0g
    syl2anc
    coeq2d
    wph
    @111
    @101
    cA
    wph
    @110
    @100
    wph
    @25
    @110
    @100
    wceq
    pwsco2mhm.f
    cR
    cS
    cF
    @100
    @107
    @115
    @100
    eqid
    #
    mhm0
    syl
    sneqd
    xpeq2d
    3eqtr3d
    wph
    @29
    @23
    @102
    @20
    wceq
    @31
    pwsco2mhm.a
    cS
    cA
    cV
    cZ
    @100
    pwsco2mhm.z
    @116
    pws0g
    syl2anc
    3eqtrd
    3jca
    vx
    vy
    cB
    @2
    @9
    @14
    cY
    cZ
    @5
    @20
    @18
    pwsco2mhm.b
    @44
    @87
    @95
    @105
    @20
    eqid
    ismhm
    sylanbrc
end
