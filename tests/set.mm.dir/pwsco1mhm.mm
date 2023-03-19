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
include "pwsmnd.mm"
include "syl2anc.mm"
include "jca.mm"
include "wb.mm"
include "eqid.mm"
include "pwselbasb.mm"
include "biimpa.mm"
include "adantr.mm"
include "fco.mm"
include "mpbird.mm"
include "fmptd.mm"
include "cof.mm"
include "cvv.mm"
include "fvexd.mm"
include "ffvelrnda.mm"
include "feqmptd.mm"
include "simprl.mm"
include "pwselbas.mm"
include "fveq2.mm"
include "fmptco.mm"
include "simprr.mm"
include "offval2.mm"
include "pwsplusgval.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "3eqtr4rd.mm"
include "mndcl.mm"
include "3expb.mm"
include "sylan.mm"
include "ovex.mm"
include "fex.mm"
include "coexg.mm"
include "sylancr.mm"
include "coeq1.mm"
include "fvmptg.mm"
include "3eqtr4d.mm"
include "ralrimivva.mm"
include "csn.mm"
include "cxp.mm"
include "mndidcl.mm"
include "syl.mm"
include "wfn.mm"
include "ffn.mm"
include "fnconstg.mm"
include "pws0g.mm"
include "fveq1d.mm"
include "fvex.mm"
include "fvconst2g.mm"
include "eqtr3d.mm"
include "fvco3.mm"
include "eqfnfvd.mm"
include "3eqtrd.mm"
include "3jca.mm"
include "ismhm.mm"
include "sylanbrc.mm"

theorem pwsco1mhm
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let vg: setvar g
  let cF: class F
  let cV: class V
  let cW: class W
  let cY: class Y
  let cZ: class Z
  let vx: setvar x
  let vz: setvar z
  let vw: setvar w
  let vy: setvar y
  assume pwsco1mhm.y: |- Y = ( R ^s A )
  assume pwsco1mhm.z: |- Z = ( R ^s B )
  assume pwsco1mhm.c: |- C = ( Base ` Z )
  assume pwsco1mhm.r: |- ( ph -> R e. Mnd )
  assume pwsco1mhm.a: |- ( ph -> A e. V )
  assume pwsco1mhm.b: |- ( ph -> B e. W )
  assume pwsco1mhm.f: |- ( ph -> F : A --> B )

  disjoint C g
  disjoint Y g
  disjoint Z g
  disjoint F g
  disjoint g ph
  disjoint x z
  disjoint A x
  disjoint A z
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint C w
  disjoint x y
  disjoint C x
  disjoint y z
  disjoint C y
  disjoint C z
  disjoint R w
  disjoint R x
  disjoint R z
  disjoint Y x
  disjoint Y y
  disjoint Z x
  disjoint Z y
  disjoint B w
  disjoint B z
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> ( g e. C |-> ( g o. F ) ) e. ( Z MndHom Y ) )

  proof
    wph
    cZ
    cmnd
    wcel
    #
    cY
    cmnd
    wcel
    #
    wa
    cC
    cY
    cbs
    cfv
    #
    vg
    cC
    vg
    cv
    #
    cF
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
    cZ
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
    cY
    cplusg
    cfv
    #
    co
    #
    wceq
    #
    vy
    cC
    wral
    vx
    cC
    wral
    #
    cZ
    c0g
    cfv
    #
    @5
    cfv
    #
    cY
    c0g
    cfv
    #
    wceq
    #
    w3a
    @5
    cZ
    cY
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
    cB
    cW
    wcel
    #
    @0
    pwsco1mhm.r
    pwsco1mhm.b
    cR
    cB
    cW
    cZ
    pwsco1mhm.z
    pwsmnd
    syl2anc
    #
    wph
    @22
    cA
    cV
    wcel
    #
    @1
    pwsco1mhm.r
    pwsco1mhm.a
    cR
    cA
    cV
    cY
    pwsco1mhm.y
    pwsmnd
    syl2anc
    jca
    wph
    @6
    @17
    @21
    wph
    vg
    cC
    @4
    @2
    @5
    wph
    @3
    cC
    wcel
    #
    wa
    #
    @4
    @2
    wcel
    #
    cA
    cR
    cbs
    cfv
    #
    @4
    wf
    #
    @27
    cB
    @29
    @3
    wf
    #
    cA
    cB
    cF
    wf
    #
    @30
    wph
    @26
    @31
    wph
    @22
    @23
    @26
    @31
    wb
    pwsco1mhm.r
    pwsco1mhm.b
    @29
    cR
    cB
    cC
    cmnd
    @3
    cZ
    cW
    pwsco1mhm.z
    @29
    eqid
    #
    pwsco1mhm.c
    pwselbasb
    syl2anc
    biimpa
    wph
    @32
    @26
    pwsco1mhm.f
    adantr
    cA
    cB
    @29
    @3
    cF
    fco
    syl2anc
    wph
    @28
    @30
    wb
    #
    @26
    wph
    @22
    @25
    @34
    pwsco1mhm.r
    pwsco1mhm.a
    @29
    cR
    cA
    @2
    cmnd
    @4
    cY
    cV
    pwsco1mhm.y
    @33
    @2
    eqid
    #
    pwselbasb
    syl2anc
    adantr
    mpbird
    @5
    eqid
    #
    fmptd
    wph
    @16
    vx
    vy
    cC
    cC
    wph
    @7
    cC
    wcel
    #
    @8
    cC
    wcel
    #
    wa
    #
    wa
    #
    @10
    cF
    ccom
    #
    @7
    cF
    ccom
    #
    @8
    cF
    ccom
    #
    @14
    co
    #
    @11
    @15
    @40
    @42
    @43
    cR
    cplusg
    cfv
    #
    cof
    #
    co
    vz
    cA
    vz
    cv
    #
    cF
    cfv
    #
    @7
    cfv
    #
    @48
    @8
    cfv
    #
    @45
    co
    #
    cmpt
    @44
    @41
    @40
    vz
    cA
    @49
    @50
    @45
    @42
    @43
    cV
    cvv
    cvv
    wph
    @25
    @39
    pwsco1mhm.a
    adantr
    #
    @40
    @47
    cA
    wcel
    wa
    #
    @48
    @7
    fvexd
    @53
    @48
    @8
    fvexd
    @40
    vz
    vw
    cA
    cB
    @48
    vw
    cv
    #
    @7
    cfv
    #
    @49
    cF
    @7
    @40
    cA
    cB
    @47
    cF
    wph
    @32
    @39
    pwsco1mhm.f
    adantr
    #
    ffvelrnda
    #
    @40
    vz
    cA
    cB
    cF
    @56
    feqmptd
    #
    @40
    vw
    cB
    @29
    @7
    @40
    @29
    cR
    cB
    cC
    cmnd
    @7
    cZ
    cW
    pwsco1mhm.z
    @33
    pwsco1mhm.c
    wph
    @22
    @39
    pwsco1mhm.r
    adantr
    #
    wph
    @23
    @39
    pwsco1mhm.b
    adantr
    #
    wph
    @37
    @38
    simprl
    #
    pwselbas
    #
    feqmptd
    #
    @54
    @48
    @7
    fveq2
    #
    fmptco
    @40
    vz
    vw
    cA
    cB
    @48
    @54
    @8
    cfv
    #
    @50
    cF
    @8
    @57
    @58
    @40
    vw
    cB
    @29
    @8
    @40
    @29
    cR
    cB
    cC
    cmnd
    @8
    cZ
    cW
    pwsco1mhm.z
    @33
    pwsco1mhm.c
    @59
    @60
    wph
    @37
    @38
    simprr
    #
    pwselbas
    #
    feqmptd
    #
    @54
    @48
    @8
    fveq2
    #
    fmptco
    offval2
    @40
    @2
    @45
    @14
    cR
    @42
    @43
    cA
    cmnd
    cV
    cY
    pwsco1mhm.y
    @35
    @59
    @52
    @40
    @42
    @2
    wcel
    #
    cA
    @29
    @42
    wf
    #
    @40
    cB
    @29
    @7
    wf
    @32
    @71
    @62
    @56
    cA
    cB
    @29
    @7
    cF
    fco
    syl2anc
    @40
    @22
    @25
    @70
    @71
    wb
    @59
    @52
    @29
    cR
    cA
    @2
    cmnd
    @42
    cY
    cV
    pwsco1mhm.y
    @33
    @35
    pwselbasb
    syl2anc
    mpbird
    @40
    @43
    @2
    wcel
    #
    cA
    @29
    @43
    wf
    #
    @40
    cB
    @29
    @8
    wf
    @32
    @73
    @67
    @56
    cA
    cB
    @29
    @8
    cF
    fco
    syl2anc
    @40
    @22
    @25
    @72
    @73
    wb
    @59
    @52
    @29
    cR
    cA
    @2
    cmnd
    @43
    cY
    cV
    pwsco1mhm.y
    @33
    @35
    pwselbasb
    syl2anc
    mpbird
    @45
    eqid
    #
    @14
    eqid
    #
    pwsplusgval
    @40
    vz
    vw
    cA
    cB
    @48
    @55
    @65
    @45
    co
    #
    @51
    cF
    @10
    @57
    @58
    @40
    @10
    @7
    @8
    @46
    co
    vw
    cB
    @76
    cmpt
    @40
    cC
    @45
    @9
    cR
    @7
    @8
    cB
    cmnd
    cW
    cZ
    pwsco1mhm.z
    pwsco1mhm.c
    @59
    @60
    @61
    @66
    @74
    @9
    eqid
    #
    pwsplusgval
    @40
    vw
    cB
    @55
    @65
    @45
    @7
    @8
    cW
    cvv
    cvv
    @60
    @40
    @54
    cB
    wcel
    wa
    #
    @54
    @7
    fvexd
    @78
    @54
    @8
    fvexd
    @63
    @68
    offval2
    eqtrd
    @54
    @48
    wceq
    @55
    @49
    @65
    @50
    @45
    @64
    @69
    oveq12d
    fmptco
    3eqtr4rd
    @40
    @10
    cC
    wcel
    #
    @41
    cvv
    wcel
    #
    @11
    @41
    wceq
    wph
    @0
    @39
    @79
    @24
    @0
    @37
    @38
    @79
    cC
    @9
    cZ
    @7
    @8
    pwsco1mhm.c
    @77
    mndcl
    3expb
    sylan
    @40
    @10
    cvv
    wcel
    cF
    cvv
    wcel
    #
    @80
    @7
    @8
    @9
    ovex
    wph
    @81
    @39
    wph
    @32
    @25
    @81
    pwsco1mhm.f
    pwsco1mhm.a
    cA
    cB
    cV
    cF
    fex
    syl2anc
    #
    adantr
    #
    @10
    cF
    cvv
    cvv
    coexg
    sylancr
    vg
    @10
    @4
    @41
    cC
    cvv
    @5
    @3
    @10
    cF
    coeq1
    @36
    fvmptg
    syl2anc
    @40
    @12
    @42
    @13
    @43
    @14
    @40
    @37
    @42
    cvv
    wcel
    #
    @12
    @42
    wceq
    @61
    @40
    @37
    @81
    @84
    @61
    @83
    @7
    cF
    cC
    cvv
    coexg
    syl2anc
    vg
    @7
    @4
    @42
    cC
    cvv
    @5
    @3
    @7
    cF
    coeq1
    @36
    fvmptg
    syl2anc
    @40
    @38
    @43
    cvv
    wcel
    #
    @13
    @43
    wceq
    @66
    @40
    @38
    @81
    @85
    @66
    @83
    @8
    cF
    cC
    cvv
    coexg
    syl2anc
    vg
    @8
    @4
    @43
    cC
    cvv
    @5
    @3
    @8
    cF
    coeq1
    @36
    fvmptg
    syl2anc
    oveq12d
    3eqtr4d
    ralrimivva
    wph
    @19
    @18
    cF
    ccom
    #
    cA
    cR
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
    cC
    wcel
    #
    @86
    cvv
    wcel
    #
    @19
    @86
    wceq
    wph
    @0
    @90
    @24
    cC
    cZ
    @18
    pwsco1mhm.c
    @18
    eqid
    #
    mndidcl
    syl
    #
    wph
    @90
    @81
    @91
    @93
    @82
    @18
    cF
    cC
    cvv
    coexg
    syl2anc
    vg
    @18
    @4
    @86
    cC
    cvv
    @5
    @3
    @18
    cF
    coeq1
    @36
    fvmptg
    syl2anc
    wph
    vx
    cA
    @86
    @89
    wph
    cA
    @29
    @86
    wf
    #
    @86
    cA
    wfn
    wph
    cB
    @29
    @18
    wf
    @32
    @94
    wph
    @29
    cR
    cB
    cC
    cmnd
    @18
    cZ
    cW
    pwsco1mhm.z
    @33
    pwsco1mhm.c
    pwsco1mhm.r
    pwsco1mhm.b
    @93
    pwselbas
    pwsco1mhm.f
    cA
    cB
    @29
    @18
    cF
    fco
    syl2anc
    cA
    @29
    @86
    ffn
    syl
    wph
    @87
    cvv
    wcel
    #
    @89
    cA
    wfn
    wph
    cR
    c0g
    fvexd
    #
    cA
    @87
    cvv
    fnconstg
    syl
    wph
    @7
    cA
    wcel
    #
    wa
    #
    @7
    cF
    cfv
    #
    @18
    cfv
    #
    @87
    @7
    @86
    cfv
    #
    @7
    @89
    cfv
    #
    @98
    @99
    cB
    @88
    cxp
    #
    cfv
    #
    @100
    @87
    wph
    @104
    @100
    wceq
    @97
    wph
    @99
    @103
    @18
    wph
    @22
    @23
    @103
    @18
    wceq
    pwsco1mhm.r
    pwsco1mhm.b
    cR
    cB
    cW
    cZ
    @87
    pwsco1mhm.z
    @87
    eqid
    #
    pws0g
    syl2anc
    fveq1d
    adantr
    @98
    @95
    @99
    cB
    wcel
    @104
    @87
    wceq
    cR
    c0g
    fvex
    wph
    cA
    cB
    @7
    cF
    pwsco1mhm.f
    ffvelrnda
    cB
    @87
    @99
    cvv
    fvconst2g
    sylancr
    eqtr3d
    wph
    @32
    @97
    @101
    @100
    wceq
    pwsco1mhm.f
    cA
    cB
    @7
    @18
    cF
    fvco3
    sylan
    wph
    @95
    @97
    @102
    @87
    wceq
    @96
    cA
    @87
    @7
    cvv
    fvconst2g
    sylan
    3eqtr4d
    eqfnfvd
    wph
    @22
    @25
    @89
    @20
    wceq
    pwsco1mhm.r
    pwsco1mhm.a
    cR
    cA
    cV
    cY
    @87
    pwsco1mhm.y
    @105
    pws0g
    syl2anc
    3eqtrd
    3jca
    vx
    vy
    cC
    @2
    @9
    @14
    cZ
    cY
    @5
    @20
    @18
    pwsco1mhm.c
    @35
    @77
    @75
    @92
    @20
    eqid
    ismhm
    sylanbrc
end
