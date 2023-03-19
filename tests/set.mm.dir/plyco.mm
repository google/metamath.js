include "ccom.mm"
include "cc.mm"
include "cc0.mm"
include "cdgr.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "ccoe.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "cmpt.mm"
include "cply.mm"
include "wcel.mm"
include "wf.mm"
include "plyf.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "feqmptd.mm"
include "wceq.mm"
include "eqid.mm"
include "coeid.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "sumeq2sdv.mm"
include "fmptco.mm"
include "cn0.mm"
include "dgrcl.mm"
include "wi.mm"
include "c1.mm"
include "caddc.mm"
include "oveq2.mm"
include "sumeq1d.mm"
include "mpteq2dv.mm"
include "eleq1d.mm"
include "imbi2d.mm"
include "csn.mm"
include "cxp.mm"
include "wa.mm"
include "cz.mm"
include "0z.mm"
include "exp0d.mm"
include "cun.mm"
include "wss.mm"
include "plybss.mm"
include "0cnd.mm"
include "snssd.mm"
include "unssd.mm"
include "coef.mm"
include "0nn0.mm"
include "ffvelrn.mm"
include "sylancl.mm"
include "sseldd.mm"
include "adantr.mm"
include "mulid1d.mm"
include "eqtrd.mm"
include "eqeltrd.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "fsum1.mm"
include "sylancr.mm"
include "mpteq2dva.mm"
include "fconstmpt.mm"
include "syl6eqr.mm"
include "plyconst.mm"
include "syl2anc.mm"
include "plyun0.mm"
include "syl6eleq.mm"
include "cof.mm"
include "simprr.mm"
include "peano2nn0.mm"
include "syl2an.mm"
include "cn.mm"
include "nn0p1nn.mm"
include "exp1d.mm"
include "eqtr4d.mm"
include "adantlr.mm"
include "plymul.mm"
include "expr.mm"
include "cvv.mm"
include "cnex.mm"
include "a1i.mm"
include "ovexd.mm"
include "eqidd.mm"
include "offval2.mm"
include "nnnn0.mm"
include "ad2antlr.mm"
include "expp1d.mm"
include "sylibd.mm"
include "expcom.mm"
include "a2d.mm"
include "nnind.mm"
include "impcom.mm"
include "adantrr.mm"
include "plyadd.mm"
include "sumex.mm"
include "fvexd.mm"
include "cuz.mm"
include "simplr.mm"
include "nn0uz.mm"
include "coef3.mm"
include "ad2antrr.mm"
include "elfznn0.mm"
include "expcl.mm"
include "mulcld.mm"
include "fsump1.mm"
include "nn0ind.mm"
include "mpcom.mm"

theorem plyco
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cF: class F
  let cG: class G
  let vd: setvar d
  let vk: setvar k
  let vz: setvar z
  assume plyco.1: |- ( ph -> F e. ( Poly ` S ) )
  assume plyco.2: |- ( ph -> G e. ( Poly ` S ) )
  assume plyco.3: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x + y ) e. S )
  assume plyco.4: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x x. y ) e. S )

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint G x
  disjoint G y
  disjoint ph x
  disjoint ph y
  disjoint S x
  disjoint S y
  disjoint d k
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint F d
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint F k
  disjoint x z
  disjoint y z
  disjoint F z
  disjoint G d
  disjoint G k
  disjoint G z
  disjoint d ph
  disjoint k ph
  disjoint ph z
  disjoint S d
  disjoint S k
  assert |- ( ph -> ( F o. G ) e. ( Poly ` S ) )

  proof
    wph
    cF
    cG
    ccom
    vz
    cc
    cc0
    cF
    cdgr
    cfv
    #
    cfz
    co
    #
    vk
    cv
    #
    cF
    ccoe
    cfv
    #
    cfv
    #
    vz
    cv
    #
    cG
    cfv
    #
    @2
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    cmpt
    #
    cS
    cply
    cfv
    #
    wph
    vz
    vx
    cc
    cc
    @6
    @1
    @4
    vx
    cv
    #
    @2
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    @9
    cG
    cF
    wph
    cc
    cc
    @5
    cG
    wph
    cG
    @11
    wcel
    #
    cc
    cc
    cG
    wf
    plyco.2
    cS
    cG
    plyf
    syl
    #
    ffvelrnda
    #
    wph
    vz
    cc
    cc
    cG
    @17
    feqmptd
    #
    wph
    cF
    @11
    wcel
    #
    cF
    vx
    cc
    @15
    cmpt
    wceq
    plyco.1
    vx
    @3
    cS
    vk
    cF
    @0
    @3
    eqid
    #
    @0
    eqid
    coeid
    syl
    @12
    @6
    wceq
    #
    @1
    @14
    @8
    vk
    @22
    @13
    @7
    @4
    cmul
    @12
    @6
    @2
    cexp
    oveq1
    oveq2d
    sumeq2sdv
    fmptco
    @0
    cn0
    wcel
    #
    wph
    @10
    @11
    wcel
    #
    wph
    @20
    @23
    plyco.1
    cS
    cF
    dgrcl
    syl
    wph
    vz
    cc
    cc0
    @12
    cfz
    co
    #
    @8
    vk
    csu
    #
    cmpt
    #
    @11
    wcel
    #
    wi
    wph
    vz
    cc
    cc0
    cc0
    cfz
    co
    #
    @8
    vk
    csu
    #
    cmpt
    #
    @11
    wcel
    #
    wi
    wph
    vz
    cc
    cc0
    vd
    cv
    #
    cfz
    co
    #
    @8
    vk
    csu
    #
    cmpt
    #
    @11
    wcel
    #
    wi
    wph
    vz
    cc
    cc0
    @33
    c1
    caddc
    co
    #
    cfz
    co
    #
    @8
    vk
    csu
    #
    cmpt
    #
    @11
    wcel
    #
    wi
    wph
    @24
    wi
    vx
    vd
    @0
    @12
    cc0
    wceq
    #
    @28
    @32
    wph
    @43
    @27
    @31
    @11
    @43
    vz
    cc
    @26
    @30
    @43
    @25
    @29
    @8
    vk
    @12
    cc0
    cc0
    cfz
    oveq2
    sumeq1d
    mpteq2dv
    eleq1d
    imbi2d
    @12
    @33
    wceq
    #
    @28
    @37
    wph
    @44
    @27
    @36
    @11
    @44
    vz
    cc
    @26
    @35
    @44
    @25
    @34
    @8
    vk
    @12
    @33
    cc0
    cfz
    oveq2
    sumeq1d
    mpteq2dv
    eleq1d
    imbi2d
    @12
    @38
    wceq
    #
    @28
    @42
    wph
    @45
    @27
    @41
    @11
    @45
    vz
    cc
    @26
    @40
    @45
    @25
    @39
    @8
    vk
    @12
    @38
    cc0
    cfz
    oveq2
    sumeq1d
    mpteq2dv
    eleq1d
    imbi2d
    @12
    @0
    wceq
    #
    @28
    @24
    wph
    @46
    @27
    @10
    @11
    @46
    vz
    cc
    @26
    @9
    @46
    @25
    @1
    @8
    vk
    @12
    @0
    cc0
    cfz
    oveq2
    sumeq1d
    mpteq2dv
    eleq1d
    imbi2d
    wph
    @31
    cc
    cc0
    @3
    cfv
    #
    csn
    cxp
    #
    @11
    wph
    @31
    vz
    cc
    @47
    cmpt
    @48
    wph
    vz
    cc
    @30
    @47
    wph
    @5
    cc
    wcel
    #
    wa
    #
    @30
    @47
    @6
    cc0
    cexp
    co
    #
    cmul
    co
    #
    @47
    @50
    cc0
    cz
    wcel
    @52
    cc
    wcel
    @30
    @52
    wceq
    0z
    @50
    @52
    @47
    cc
    @50
    @52
    @47
    c1
    cmul
    co
    @47
    @50
    @51
    c1
    @47
    cmul
    @50
    @6
    @18
    exp0d
    oveq2d
    @50
    @47
    wph
    @47
    cc
    wcel
    @49
    wph
    cS
    cc0
    csn
    #
    cun
    #
    cc
    @47
    wph
    cS
    @53
    cc
    wph
    @20
    cS
    cc
    wss
    plyco.1
    cS
    cF
    plybss
    syl
    wph
    cc0
    cc
    wph
    0cnd
    snssd
    unssd
    #
    wph
    cn0
    @54
    @3
    wf
    #
    cc0
    cn0
    wcel
    @47
    @54
    wcel
    #
    wph
    @20
    @56
    plyco.1
    @3
    cS
    cF
    @21
    coef
    syl
    #
    0nn0
    cn0
    @54
    cc0
    @3
    ffvelrn
    sylancl
    #
    sseldd
    adantr
    #
    mulid1d
    eqtrd
    #
    @60
    eqeltrd
    @8
    @52
    vk
    cc0
    @2
    cc0
    wceq
    @4
    @47
    @7
    @51
    cmul
    @2
    cc0
    @3
    fveq2
    @2
    cc0
    @6
    cexp
    oveq2
    oveq12d
    fsum1
    sylancr
    @61
    eqtrd
    mpteq2dva
    vz
    cc
    @47
    fconstmpt
    syl6eqr
    wph
    @48
    @54
    cply
    cfv
    #
    @11
    wph
    @54
    cc
    wss
    #
    @57
    @48
    @62
    wcel
    @55
    @59
    @47
    @54
    plyconst
    syl2anc
    cS
    plyun0
    #
    syl6eleq
    eqeltrd
    @33
    cn0
    wcel
    #
    wph
    @37
    @42
    wph
    @65
    @37
    @42
    wi
    wph
    @65
    wa
    #
    @37
    @36
    cc
    @38
    @3
    cfv
    #
    csn
    cxp
    #
    vz
    cc
    @6
    @38
    cexp
    co
    #
    cmpt
    #
    cmul
    cof
    #
    co
    #
    caddc
    cof
    co
    #
    @11
    wcel
    #
    @42
    wph
    @65
    @37
    @74
    wph
    @65
    @37
    wa
    #
    wa
    vx
    vy
    cS
    @36
    @72
    wph
    @65
    @37
    simprr
    wph
    @65
    @72
    @11
    wcel
    @37
    @66
    vx
    vy
    cS
    @68
    @70
    @66
    @68
    @62
    @11
    @66
    @63
    @67
    @54
    wcel
    #
    @68
    @62
    wcel
    wph
    @63
    @65
    @55
    adantr
    wph
    @56
    @38
    cn0
    wcel
    @76
    @65
    @58
    @33
    peano2nn0
    cn0
    @54
    @38
    @3
    ffvelrn
    syl2an
    @67
    @54
    plyconst
    syl2anc
    @64
    syl6eleq
    @65
    wph
    @70
    @11
    wcel
    #
    @65
    @38
    cn
    wcel
    wph
    @77
    wi
    #
    @33
    nn0p1nn
    wph
    vz
    cc
    @6
    @12
    cexp
    co
    #
    cmpt
    #
    @11
    wcel
    #
    wi
    wph
    vz
    cc
    @6
    c1
    cexp
    co
    #
    cmpt
    #
    @11
    wcel
    #
    wi
    wph
    vz
    cc
    @6
    @33
    cexp
    co
    #
    cmpt
    #
    @11
    wcel
    #
    wi
    @78
    @78
    vx
    vd
    @38
    @12
    c1
    wceq
    #
    @81
    @84
    wph
    @88
    @80
    @83
    @11
    @88
    vz
    cc
    @79
    @82
    @12
    c1
    @6
    cexp
    oveq2
    mpteq2dv
    eleq1d
    imbi2d
    @44
    @81
    @87
    wph
    @44
    @80
    @86
    @11
    @44
    vz
    cc
    @79
    @85
    @12
    @33
    @6
    cexp
    oveq2
    mpteq2dv
    eleq1d
    imbi2d
    @45
    @81
    @77
    wph
    @45
    @80
    @70
    @11
    @45
    vz
    cc
    @79
    @69
    @12
    @38
    @6
    cexp
    oveq2
    mpteq2dv
    eleq1d
    imbi2d
    #
    @89
    wph
    @83
    cG
    @11
    wph
    @83
    vz
    cc
    @6
    cmpt
    #
    cG
    wph
    vz
    cc
    @82
    @6
    @50
    @6
    @18
    exp1d
    mpteq2dva
    @19
    eqtr4d
    plyco.2
    eqeltrd
    @33
    cn
    wcel
    #
    wph
    @87
    @77
    wph
    @91
    @87
    @77
    wi
    wph
    @91
    wa
    #
    @87
    @86
    cG
    @71
    co
    #
    @11
    wcel
    #
    @77
    wph
    @91
    @87
    @94
    wph
    @91
    @87
    wa
    #
    wa
    vx
    vy
    cS
    @86
    cG
    wph
    @91
    @87
    simprr
    wph
    @16
    @95
    plyco.2
    adantr
    wph
    @12
    cS
    wcel
    vy
    cv
    #
    cS
    wcel
    wa
    #
    @12
    @96
    caddc
    co
    cS
    wcel
    #
    @95
    plyco.3
    adantlr
    wph
    @97
    @12
    @96
    cmul
    co
    cS
    wcel
    #
    @95
    plyco.4
    adantlr
    plymul
    expr
    @92
    @93
    @70
    @11
    @92
    @93
    vz
    cc
    @85
    @6
    cmul
    co
    #
    cmpt
    @70
    @92
    vz
    cc
    @85
    @6
    cmul
    @86
    cG
    cvv
    cvv
    cc
    cc
    cvv
    wcel
    #
    @92
    cnex
    a1i
    @92
    @49
    wa
    #
    @6
    @33
    cexp
    ovexd
    wph
    @49
    @6
    cc
    wcel
    #
    @91
    @18
    adantlr
    #
    @92
    @86
    eqidd
    wph
    cG
    @90
    wceq
    @91
    @19
    adantr
    offval2
    @92
    vz
    cc
    @69
    @100
    @102
    @6
    @33
    @104
    @91
    @65
    wph
    @49
    @33
    nnnn0
    ad2antlr
    expp1d
    mpteq2dva
    eqtr4d
    eleq1d
    sylibd
    expcom
    a2d
    nnind
    syl
    impcom
    wph
    @97
    @98
    @65
    plyco.3
    adantlr
    wph
    @97
    @99
    @65
    plyco.4
    adantlr
    plymul
    adantrr
    wph
    @97
    @98
    @75
    plyco.3
    adantlr
    plyadd
    expr
    @66
    @73
    @41
    @11
    @66
    @73
    vz
    cc
    @35
    @67
    @69
    cmul
    co
    #
    caddc
    co
    #
    cmpt
    @41
    @66
    vz
    cc
    @35
    @105
    caddc
    @36
    @72
    cvv
    cvv
    cvv
    @101
    @66
    cnex
    a1i
    #
    @35
    cvv
    wcel
    @66
    @49
    wa
    #
    @34
    @8
    vk
    sumex
    a1i
    @108
    @67
    @69
    cmul
    ovexd
    @66
    @36
    eqidd
    @66
    vz
    cc
    @67
    @69
    cmul
    @68
    @70
    cvv
    cvv
    cvv
    @107
    @108
    @38
    @3
    fvexd
    @108
    @6
    @38
    cexp
    ovexd
    @68
    vz
    cc
    @67
    cmpt
    wceq
    @66
    vz
    cc
    @67
    fconstmpt
    a1i
    @66
    @70
    eqidd
    offval2
    offval2
    @66
    vz
    cc
    @40
    @106
    @108
    @8
    @105
    vk
    cc0
    @33
    @108
    @33
    cn0
    cc0
    cuz
    cfv
    wph
    @65
    @49
    simplr
    nn0uz
    syl6eleq
    @108
    @2
    @39
    wcel
    #
    wa
    @4
    @7
    @108
    cn0
    cc
    @3
    wf
    #
    @2
    cn0
    wcel
    #
    @4
    cc
    wcel
    @109
    wph
    @110
    @65
    @49
    wph
    @20
    @110
    plyco.1
    @3
    cS
    cF
    @21
    coef3
    syl
    ad2antrr
    @2
    @38
    elfznn0
    #
    cn0
    cc
    @2
    @3
    ffvelrn
    syl2an
    @108
    @103
    @111
    @7
    cc
    wcel
    @109
    wph
    @49
    @103
    @65
    @18
    adantlr
    @112
    @6
    @2
    expcl
    syl2an
    mulcld
    @2
    @38
    wceq
    @4
    @67
    @7
    @69
    cmul
    @2
    @38
    @3
    fveq2
    @2
    @38
    @6
    cexp
    oveq2
    oveq12d
    fsump1
    mpteq2dva
    eqtr4d
    eleq1d
    sylibd
    expcom
    a2d
    nn0ind
    mpcom
    eqeltrd
end
