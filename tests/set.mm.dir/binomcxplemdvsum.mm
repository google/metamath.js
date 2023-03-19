include "cc.mm"
include "cdv.mm"
include "co.mm"
include "cn.mm"
include "cv.mm"
include "cfv.mm"
include "csu.mm"
include "cmpt.mm"
include "cmul.mm"
include "c1.mm"
include "cmin.mm"
include "cexp.mm"
include "cc0.mm"
include "cabs.mm"
include "caddc.mm"
include "cn0.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "wcel.mm"
include "cr.mm"
include "crab.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "c2.mm"
include "cdiv.mm"
include "cif.mm"
include "ccom.mm"
include "cbl.mm"
include "ccnv.mm"
include "cico.mm"
include "cima.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nffv.mm"
include "nfseq.mm"
include "nfel1.mm"
include "nfrab.mm"
include "nfsup.mm"
include "nfov.mm"
include "nfima.mm"
include "nfsum.mm"
include "wceq.mm"
include "wa.mm"
include "simpl.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "sumeq2dv.mm"
include "nfmpt.mm"
include "fveq2.mm"
include "cbvsumi.mm"
include "syl6eq.mm"
include "cbvmptf.mm"
include "eqtri.mm"
include "cbcc.mm"
include "cvv.mm"
include "ovexd.mm"
include "a1i.mm"
include "simpr.mm"
include "oveq2d.mm"
include "adantr.mm"
include "bcccl.mm"
include "fvmptd.mm"
include "eqeltrd.mm"
include "fmpt2d.mm"
include "nfv.mm"
include "seqeq3d.mm"
include "eleq1d.mm"
include "cbvrab.mm"
include "supeq1i.mm"
include "fveq1i.mm"
include "seqeq3.mm"
include "ax-mp.mm"
include "eleq1i.mm"
include "rabbii.mm"
include "3eqtrri.mm"
include "oveq2i.mm"
include "oveq1i.mm"
include "eqid.mm"
include "ifbieq12i.mm"
include "oveq1.mm"
include "mpteq2dv.mm"
include "cbvmptv.mm"
include "pserdv2.mm"
include "cnvimass.mm"
include "eqsstri.mm"
include "absf.mm"
include "fdmi.mm"
include "sseqtri.mm"
include "sseli.mm"
include "simplr.mm"
include "oveq1d.mm"
include "mpteq2dva.mm"
include "nnex.mm"
include "mptex.mm"
include "oveq12d.mm"
include "sylan2.mm"
include "eqtr4d.mm"

theorem binomcxplemdvsum
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let vj: setvar j
  let vk: setvar k
  let cE: class E
  let cF: class F
  let vr: setvar r
  let vb: setvar b
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assume binomcxp.a: |- ( ph -> A e. RR+ )
  assume binomcxp.b: |- ( ph -> B e. RR )
  assume binomcxp.lt: |- ( ph -> ( abs ` B ) < ( abs ` A ) )
  assume binomcxp.c: |- ( ph -> C e. CC )
  assume binomcxplem.f: |- F = ( j e. NN0 |-> ( C _Cc j ) )
  assume binomcxplem.s: |- S = ( b e. CC |-> ( k e. NN0 |-> ( ( F ` k ) x. ( b ^ k ) ) ) )
  assume binomcxplem.r: |- R = sup ( { r e. RR | seq 0 ( + , ( S ` r ) ) e. dom ~~> } , RR* , < )
  assume binomcxplem.e: |- E = ( b e. CC |-> ( k e. NN |-> ( ( k x. ( F ` k ) ) x. ( b ^ ( k - 1 ) ) ) ) )
  assume binomcxplem.d: |- D = ( `' abs " ( 0 [,) R ) )
  assume binomcxplem.p: |- P = ( b e. D |-> sum_ k e. NN0 ( ( S ` b ) ` k ) )

  disjoint b k
  disjoint F b
  disjoint F k
  disjoint b ph
  disjoint k ph
  disjoint b r
  disjoint k r
  disjoint F r
  disjoint j k
  disjoint j ph
  disjoint C j
  disjoint b m
  disjoint b n
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint F m
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint m ph
  disjoint n ph
  disjoint ph x
  disjoint ph y
  disjoint b w
  disjoint k w
  disjoint m w
  disjoint n w
  disjoint w y
  disjoint F w
  disjoint D m
  disjoint D n
  disjoint D x
  disjoint D y
  disjoint r z
  disjoint S m
  disjoint S n
  disjoint S y
  disjoint S z
  disjoint E n
  disjoint E y
  disjoint P x
  assert |- ( ph -> ( CC _D P ) = ( b e. D |-> sum_ k e. NN ( ( E ` b ) ` k ) ) )

  proof
    wph
    cc
    cP
    cdv
    co
    #
    vy
    cD
    cn
    vn
    cv
    #
    vy
    cv
    #
    cE
    cfv
    #
    cfv
    #
    vn
    csu
    #
    cmpt
    #
    vb
    cD
    cn
    vk
    cv
    #
    vb
    cv
    #
    cE
    cfv
    #
    cfv
    #
    vk
    csu
    #
    cmpt
    wph
    @0
    vy
    cD
    cn
    @1
    @1
    cF
    cfv
    #
    cmul
    co
    #
    @2
    @1
    c1
    cmin
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    vn
    csu
    #
    cmpt
    @6
    wph
    vb
    vy
    cF
    cc0
    vx
    cv
    cabs
    cfv
    #
    caddc
    vz
    cv
    #
    vw
    cc
    vk
    cn0
    @7
    cF
    cfv
    #
    vw
    cv
    #
    @7
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    #
    cmpt
    #
    cfv
    #
    cc0
    cseq
    #
    cli
    cdm
    #
    wcel
    #
    vz
    cr
    crab
    #
    cxr
    clt
    csup
    #
    cr
    wcel
    #
    @18
    @31
    caddc
    co
    #
    c2
    cdiv
    co
    #
    @18
    c1
    caddc
    co
    #
    cif
    #
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cabs
    cmin
    ccom
    cbl
    cfv
    #
    co
    cR
    cD
    vm
    vn
    vk
    cP
    cS
    caddc
    @19
    vb
    cc
    vk
    cn0
    @20
    @8
    @7
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    #
    cmpt
    #
    cfv
    #
    cc0
    cseq
    #
    @28
    wcel
    #
    vz
    cr
    crab
    #
    cxr
    clt
    csup
    #
    cr
    wcel
    #
    @18
    @48
    caddc
    co
    #
    c2
    cdiv
    co
    #
    @35
    cif
    #
    vz
    vx
    binomcxplem.s
    cP
    vb
    cD
    cn0
    @7
    @8
    cS
    cfv
    #
    cfv
    #
    vk
    csu
    #
    cmpt
    vy
    cD
    cn0
    vm
    cv
    #
    @2
    cS
    cfv
    #
    cfv
    #
    vm
    csu
    #
    cmpt
    binomcxplem.p
    vb
    vy
    cD
    @55
    @59
    vb
    cD
    cabs
    ccnv
    #
    cc0
    cR
    cico
    co
    #
    cima
    #
    binomcxplem.d
    vb
    @60
    @61
    vb
    @60
    nfcv
    vb
    cc0
    cR
    cico
    vb
    cc0
    nfcv
    #
    vb
    cico
    nfcv
    vb
    cR
    caddc
    vr
    cv
    #
    cS
    cfv
    #
    cc0
    cseq
    #
    @28
    wcel
    #
    vr
    cr
    crab
    #
    cxr
    clt
    csup
    #
    binomcxplem.r
    vb
    @68
    cxr
    clt
    @67
    vb
    vr
    cr
    vb
    @66
    @28
    vb
    caddc
    @65
    cc0
    @63
    vb
    caddc
    nfcv
    vb
    @64
    cS
    vb
    cS
    @43
    binomcxplem.s
    vb
    cc
    @42
    nfmpt1
    nfcxfr
    #
    vb
    @64
    nfcv
    nffv
    nfseq
    nfel1
    vb
    cr
    nfcv
    nfrab
    vb
    cxr
    nfcv
    vb
    clt
    nfcv
    nfsup
    nfcxfr
    nfov
    nfima
    nfcxfr
    #
    vy
    cD
    nfcv
    #
    vy
    @55
    nfcv
    vb
    cn0
    @58
    vm
    vb
    cn0
    nfcv
    vb
    @56
    @57
    vb
    @2
    cS
    @70
    vb
    @2
    nfcv
    #
    nffv
    vb
    @56
    nfcv
    nffv
    nfsum
    @8
    @2
    wceq
    #
    @55
    cn0
    @7
    @57
    cfv
    #
    vk
    csu
    @59
    @74
    cn0
    @54
    @75
    vk
    @74
    @7
    cn0
    wcel
    #
    wa
    #
    @7
    @53
    @57
    @77
    @8
    @2
    cS
    @74
    @76
    simpl
    fveq2d
    fveq1d
    sumeq2dv
    cn0
    @75
    @58
    vk
    vm
    vm
    @75
    nfcv
    vk
    @56
    @57
    vk
    @2
    cS
    vk
    cS
    @43
    binomcxplem.s
    vk
    vb
    cc
    @42
    vk
    cc
    nfcv
    #
    vk
    cn0
    @41
    nfmpt1
    nfmpt
    nfcxfr
    vk
    @2
    nfcv
    nffv
    vk
    @56
    nfcv
    nffv
    @7
    @56
    @57
    fveq2
    cbvsumi
    syl6eq
    cbvmptf
    eqtri
    wph
    vj
    vk
    cn0
    cC
    vj
    cv
    #
    cbcc
    co
    #
    cc
    cF
    cvv
    wph
    @79
    cn0
    wcel
    wa
    cC
    @79
    cbcc
    ovexd
    cF
    vj
    cn0
    @80
    cmpt
    wceq
    #
    wph
    binomcxplem.f
    a1i
    wph
    @76
    wa
    #
    @20
    cC
    @7
    cbcc
    co
    #
    cc
    @82
    vj
    @7
    @80
    @83
    cn0
    cF
    cc
    @81
    @82
    binomcxplem.f
    a1i
    @82
    @79
    @7
    wceq
    #
    wa
    @79
    @7
    cC
    cbcc
    @82
    @84
    simpr
    oveq2d
    wph
    @76
    simpr
    #
    @82
    cC
    @7
    wph
    cC
    cc
    wcel
    @76
    binomcxp.c
    adantr
    @85
    bcccl
    #
    fvmptd
    @86
    eqeltrd
    fmpt2d
    cR
    @69
    caddc
    @19
    cS
    cfv
    #
    cc0
    cseq
    #
    @28
    wcel
    #
    vz
    cr
    crab
    #
    cxr
    clt
    csup
    #
    binomcxplem.r
    cxr
    @68
    @90
    clt
    @67
    @89
    vr
    vz
    cr
    vr
    cr
    nfcv
    vz
    cr
    nfcv
    @67
    vz
    nfv
    vr
    @88
    @28
    vr
    caddc
    @87
    cc0
    vr
    cc0
    nfcv
    vr
    caddc
    nfcv
    vr
    @19
    cS
    vr
    cS
    @43
    binomcxplem.s
    vr
    @43
    nfcv
    nfcxfr
    vr
    @19
    nfcv
    nffv
    nfseq
    nfel1
    @64
    @19
    wceq
    #
    @66
    @88
    @28
    @92
    @65
    @87
    caddc
    cc0
    @64
    @19
    cS
    fveq2
    seqeq3d
    eleq1d
    cbvrab
    supeq1i
    #
    eqtri
    binomcxplem.d
    @49
    cR
    cr
    wcel
    @51
    @35
    @18
    cR
    caddc
    co
    #
    c2
    cdiv
    co
    @35
    @48
    cR
    cr
    cR
    @69
    @91
    @48
    binomcxplem.r
    @93
    cxr
    @90
    @47
    clt
    @89
    @46
    vz
    cr
    @88
    @45
    @28
    @87
    @44
    wceq
    @88
    @45
    wceq
    @19
    cS
    @43
    binomcxplem.s
    fveq1i
    caddc
    @87
    @44
    cc0
    seqeq3
    ax-mp
    eleq1i
    rabbii
    supeq1i
    3eqtrri
    #
    eleq1i
    @50
    @94
    c2
    cdiv
    @48
    cR
    @18
    caddc
    @95
    oveq2i
    oveq1i
    @35
    eqid
    #
    ifbieq12i
    @38
    @18
    @52
    caddc
    co
    #
    c2
    cdiv
    co
    cc0
    @39
    @37
    @97
    c2
    cdiv
    @36
    @52
    @18
    caddc
    @32
    @49
    @34
    @35
    @51
    @35
    @31
    @48
    cr
    cxr
    @30
    @47
    clt
    @29
    @46
    vz
    cr
    @27
    @45
    @28
    @26
    @44
    wceq
    @27
    @45
    wceq
    @19
    @25
    @43
    vw
    vb
    cc
    @24
    @42
    @21
    @8
    wceq
    #
    vk
    cn0
    @23
    @41
    @98
    @22
    @40
    @20
    cmul
    @21
    @8
    @7
    cexp
    oveq1
    oveq2d
    mpteq2dv
    cbvmptv
    fveq1i
    caddc
    @26
    @44
    cc0
    seqeq3
    ax-mp
    eleq1i
    rabbii
    supeq1i
    #
    eleq1i
    @33
    @50
    c2
    cdiv
    @31
    @48
    @18
    caddc
    @99
    oveq2i
    oveq1i
    @96
    ifbieq12i
    oveq2i
    oveq1i
    oveq2i
    pserdv2
    wph
    vy
    cD
    @5
    @17
    @2
    cD
    wcel
    wph
    @2
    cc
    wcel
    #
    @5
    @17
    wceq
    cD
    cc
    @2
    cD
    cabs
    cdm
    #
    cc
    cD
    @62
    @101
    binomcxplem.d
    cabs
    @61
    cnvimass
    eqsstri
    cc
    cr
    cabs
    absf
    fdmi
    sseqtri
    sseli
    wph
    @100
    wa
    #
    cn
    @4
    @16
    vn
    @102
    @1
    cn
    wcel
    #
    wa
    #
    vk
    @1
    @7
    @20
    cmul
    co
    #
    @2
    @7
    c1
    cmin
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    @16
    cn
    @3
    cvv
    @102
    @3
    vk
    cn
    @108
    cmpt
    #
    wceq
    @103
    @102
    vb
    @2
    vk
    cn
    @105
    @8
    @106
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    #
    @109
    cc
    cE
    cvv
    cE
    vb
    cc
    @112
    cmpt
    #
    wceq
    @102
    binomcxplem.e
    a1i
    @102
    @74
    wa
    #
    vk
    cn
    @111
    @108
    @114
    @7
    cn
    wcel
    #
    wa
    #
    @110
    @107
    @105
    cmul
    @116
    @8
    @2
    @106
    cexp
    @102
    @74
    @115
    simplr
    oveq1d
    oveq2d
    mpteq2dva
    wph
    @100
    simpr
    @109
    cvv
    wcel
    @102
    vk
    cn
    @108
    nnex
    mptex
    a1i
    fvmptd
    adantr
    @104
    @7
    @1
    wceq
    #
    wa
    #
    @105
    @13
    @107
    @15
    cmul
    @118
    @7
    @1
    @20
    @12
    cmul
    @104
    @117
    simpr
    #
    @118
    @7
    @1
    cF
    @119
    fveq2d
    oveq12d
    @118
    @106
    @14
    @2
    cexp
    @118
    @7
    @1
    c1
    cmin
    @119
    oveq1d
    oveq2d
    oveq12d
    @102
    @103
    simpr
    @104
    @13
    @15
    cmul
    ovexd
    fvmptd
    sumeq2dv
    sylan2
    mpteq2dva
    eqtr4d
    vy
    vb
    cD
    @5
    @11
    @72
    @71
    vb
    cn
    @4
    vn
    vb
    cn
    nfcv
    vb
    @1
    @3
    vb
    @2
    cE
    vb
    cE
    @113
    binomcxplem.e
    vb
    cc
    @112
    nfmpt1
    nfcxfr
    @73
    nffv
    vb
    @1
    nfcv
    nffv
    nfsum
    vy
    @11
    nfcv
    @2
    @8
    wceq
    #
    @5
    cn
    @1
    @9
    cfv
    #
    vn
    csu
    @11
    @120
    cn
    @4
    @121
    vn
    @120
    @103
    wa
    #
    @1
    @3
    @9
    @122
    @2
    @8
    cE
    @120
    @103
    simpl
    fveq2d
    fveq1d
    sumeq2dv
    cn
    @121
    @10
    vn
    vk
    vk
    @1
    @9
    vk
    @8
    cE
    vk
    cE
    @113
    binomcxplem.e
    vk
    vb
    cc
    @112
    @78
    vk
    cn
    @111
    nfmpt1
    nfmpt
    nfcxfr
    vk
    @8
    nfcv
    nffv
    vk
    @1
    nfcv
    nffv
    vn
    @10
    nfcv
    @1
    @7
    @9
    fveq2
    cbvsumi
    syl6eq
    cbvmptf
    syl6eq
end
