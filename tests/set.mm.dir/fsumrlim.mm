include "wss.mm"
include "csu.mm"
include "cmpt.mm"
include "crli.mm"
include "wbr.mm"
include "ssid.mm"
include "cfn.mm"
include "wcel.mm"
include "wi.mm"
include "cv.mm"
include "c0.mm"
include "cc0.mm"
include "csn.mm"
include "cun.mm"
include "wceq.mm"
include "sseq1.mm"
include "sumeq1.mm"
include "sum0.mm"
include "syl6eq.mm"
include "mpteq2dv.mm"
include "breq12d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "weq.mm"
include "cr.mm"
include "cc.mm"
include "0cn.mm"
include "rlimconst.mm"
include "sylancl.mm"
include "a1d.mm"
include "wn.mm"
include "wa.mm"
include "ssun1.mm"
include "sstr.mm"
include "mpan.mm"
include "imim1i.mm"
include "csb.mm"
include "caddc.mm"
include "co.mm"
include "cvv.mm"
include "sumex.mm"
include "a1i.mm"
include "wral.mm"
include "simprr.mm"
include "unssbd.mm"
include "vex.mm"
include "snss.mm"
include "sylibr.mm"
include "adantr.mm"
include "anass1rs.mm"
include "rlimmptrcl.mm"
include "an32s.mm"
include "adantllr.mm"
include "ralrimiva.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "rspc.mm"
include "sylc.mm"
include "mpan9.mm"
include "elex.mm"
include "syl.mm"
include "nfcv.mm"
include "nfsum.mm"
include "sumeq2sdv.mm"
include "cbvmpt.mm"
include "simpr.mm"
include "syl5eqbrr.mm"
include "nfmpt.mm"
include "nfbr.mm"
include "rlimadd.mm"
include "cin.mm"
include "simprl.mm"
include "disjsn.mm"
include "eqidd.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "sselda.mm"
include "adantlr.mm"
include "syldan.mm"
include "fsumsplit.mm"
include "cbvsumi.mm"
include "csbeq1.mm"
include "sumsn.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "nfov.mm"
include "oveq12d.mm"
include "rlimcl.mm"
include "3brtr4d.mm"
include "ex.mm"
include "expr.mm"
include "a2d.mm"
include "syl5.mm"
include "expcom.mm"
include "adantl.mm"
include "findcard2s.mm"
include "mpcom.mm"
include "mpi.mm"

theorem fsumrlim
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  let cV: class V
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume fsumrlim.1: |- ( ph -> A C_ RR )
  assume fsumrlim.2: |- ( ph -> B e. Fin )
  assume fsumrlim.3: |- ( ( ph /\ ( x e. A /\ k e. B ) ) -> C e. V )
  assume fsumrlim.4: |- ( ( ph /\ k e. B ) -> ( x e. A |-> C ) ~~>r D )

  disjoint k x
  disjoint A k
  disjoint A x
  disjoint B k
  disjoint B x
  disjoint k ph
  disjoint ph x
  disjoint k w
  disjoint k y
  disjoint k z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint C w
  disjoint C y
  disjoint C z
  disjoint ph w
  disjoint ph y
  disjoint ph z
  disjoint D w
  disjoint D y
  disjoint D z
  assert |- ( ph -> ( x e. A |-> sum_ k e. B C ) ~~>r sum_ k e. B D )

  proof
    wph
    cB
    cB
    wss
    #
    vx
    cA
    cB
    cC
    vk
    csu
    #
    cmpt
    #
    cB
    cD
    vk
    csu
    #
    crli
    wbr
    #
    cB
    ssid
    cB
    cfn
    wcel
    #
    wph
    @0
    @4
    wi
    #
    fsumrlim.2
    wph
    vw
    cv
    #
    cB
    wss
    #
    vx
    cA
    @7
    cC
    vk
    csu
    #
    cmpt
    #
    @7
    cD
    vk
    csu
    #
    crli
    wbr
    #
    wi
    #
    wi
    wph
    c0
    cB
    wss
    #
    vx
    cA
    cc0
    cmpt
    #
    cc0
    crli
    wbr
    #
    wi
    #
    wi
    wph
    vy
    cv
    #
    cB
    wss
    #
    vx
    cA
    @18
    cC
    vk
    csu
    #
    cmpt
    #
    @18
    cD
    vk
    csu
    #
    crli
    wbr
    #
    wi
    #
    wi
    #
    wph
    @18
    vz
    cv
    #
    csn
    #
    cun
    #
    cB
    wss
    #
    vx
    cA
    @28
    cC
    vk
    csu
    #
    cmpt
    #
    @28
    cD
    vk
    csu
    #
    crli
    wbr
    #
    wi
    #
    wi
    #
    wph
    @6
    wi
    vw
    vy
    vz
    cB
    @7
    c0
    wceq
    #
    @13
    @17
    wph
    @36
    @8
    @14
    @12
    @16
    @7
    c0
    cB
    sseq1
    @36
    @10
    @15
    @11
    cc0
    crli
    @36
    vx
    cA
    @9
    cc0
    @36
    @9
    c0
    cC
    vk
    csu
    cc0
    @7
    c0
    cC
    vk
    sumeq1
    cC
    vk
    sum0
    syl6eq
    mpteq2dv
    @36
    @11
    c0
    cD
    vk
    csu
    cc0
    @7
    c0
    cD
    vk
    sumeq1
    cD
    vk
    sum0
    syl6eq
    breq12d
    imbi12d
    imbi2d
    vw
    vy
    weq
    #
    @13
    @24
    wph
    @37
    @8
    @19
    @12
    @23
    @7
    @18
    cB
    sseq1
    @37
    @10
    @21
    @11
    @22
    crli
    @37
    vx
    cA
    @9
    @20
    @7
    @18
    cC
    vk
    sumeq1
    mpteq2dv
    @7
    @18
    cD
    vk
    sumeq1
    breq12d
    imbi12d
    imbi2d
    @7
    @28
    wceq
    #
    @13
    @34
    wph
    @38
    @8
    @29
    @12
    @33
    @7
    @28
    cB
    sseq1
    @38
    @10
    @31
    @11
    @32
    crli
    @38
    vx
    cA
    @9
    @30
    @7
    @28
    cC
    vk
    sumeq1
    mpteq2dv
    @7
    @28
    cD
    vk
    sumeq1
    breq12d
    imbi12d
    imbi2d
    @7
    cB
    wceq
    #
    @13
    @6
    wph
    @39
    @8
    @0
    @12
    @4
    @7
    cB
    cB
    sseq1
    @39
    @10
    @2
    @11
    @3
    crli
    @39
    vx
    cA
    @9
    @1
    @7
    cB
    cC
    vk
    sumeq1
    mpteq2dv
    @7
    cB
    cD
    vk
    sumeq1
    breq12d
    imbi12d
    imbi2d
    wph
    @16
    @14
    wph
    cA
    cr
    wss
    cc0
    cc
    wcel
    @16
    fsumrlim.1
    0cn
    vx
    cA
    cc0
    rlimconst
    sylancl
    a1d
    @26
    @18
    wcel
    wn
    #
    @25
    @35
    wi
    @18
    cfn
    wcel
    @40
    wph
    @24
    @34
    wph
    @40
    @24
    @34
    wi
    @24
    @29
    @23
    wi
    wph
    @40
    wa
    #
    @34
    @29
    @19
    @23
    @18
    @28
    wss
    @29
    @19
    @18
    @27
    ssun1
    @18
    @28
    cB
    sstr
    mpan
    imim1i
    @41
    @29
    @23
    @33
    wph
    @40
    @29
    @23
    @33
    wi
    wph
    @40
    @29
    wa
    #
    wa
    #
    @23
    @33
    @43
    @23
    wa
    #
    vw
    cA
    @18
    vx
    @7
    cC
    csb
    #
    vk
    csu
    #
    vx
    @7
    vk
    @26
    cC
    csb
    #
    csb
    #
    caddc
    co
    #
    cmpt
    #
    @22
    vk
    @26
    cD
    csb
    #
    caddc
    co
    #
    @31
    @32
    crli
    @44
    vw
    cA
    @46
    @48
    @22
    @51
    cvv
    @46
    cvv
    wcel
    @44
    @7
    cA
    wcel
    #
    wa
    #
    @18
    @45
    vk
    sumex
    a1i
    @54
    @48
    cc
    wcel
    #
    @48
    cvv
    wcel
    @44
    @47
    cc
    wcel
    #
    vx
    cA
    wral
    #
    @53
    @55
    @43
    @57
    @23
    @43
    @56
    vx
    cA
    @43
    vx
    cv
    cA
    wcel
    #
    wa
    #
    @26
    cB
    wcel
    #
    cC
    cc
    wcel
    #
    vk
    cB
    wral
    @56
    @43
    @60
    @58
    @43
    @27
    cB
    wss
    @60
    @43
    @18
    @27
    cB
    wph
    @40
    @29
    simprr
    #
    unssbd
    @26
    cB
    vz
    vex
    snss
    sylibr
    #
    adantr
    #
    @59
    @61
    vk
    cB
    wph
    @58
    vk
    cv
    #
    cB
    wcel
    #
    @61
    @42
    wph
    @66
    @58
    @61
    wph
    @66
    wa
    #
    cA
    cC
    cD
    vx
    cV
    wph
    @58
    @66
    cC
    cV
    wcel
    fsumrlim.3
    anass1rs
    fsumrlim.4
    rlimmptrcl
    an32s
    adantllr
    #
    ralrimiva
    @61
    @56
    vk
    @26
    cB
    vk
    @47
    cc
    vk
    @26
    cC
    nfcsb1v
    #
    nfel1
    vk
    vz
    weq
    #
    cC
    @47
    cc
    vk
    @26
    cC
    csbeq1a
    #
    eleq1d
    rspc
    sylc
    #
    ralrimiva
    adantr
    @56
    @55
    vx
    @7
    cA
    vx
    @48
    cc
    vx
    @7
    @47
    nfcsb1v
    #
    nfel1
    vx
    vw
    weq
    #
    @47
    @48
    cc
    vx
    @7
    @47
    csbeq1a
    #
    eleq1d
    rspc
    mpan9
    @48
    cc
    elex
    syl
    @44
    vw
    cA
    @46
    cmpt
    @21
    @22
    crli
    vx
    vw
    cA
    @20
    @46
    vw
    @20
    nfcv
    vx
    @18
    @45
    vk
    vx
    @18
    nfcv
    vx
    @7
    cC
    nfcsb1v
    nfsum
    #
    @74
    @18
    cC
    @45
    vk
    vx
    @7
    cC
    csbeq1a
    sumeq2sdv
    #
    cbvmpt
    @43
    @23
    simpr
    syl5eqbrr
    @44
    vw
    cA
    @48
    cmpt
    vx
    cA
    @47
    cmpt
    #
    @51
    crli
    vx
    vw
    cA
    @47
    @48
    vw
    @47
    nfcv
    @73
    @75
    cbvmpt
    @43
    @78
    @51
    crli
    wbr
    #
    @23
    @43
    @60
    vx
    cA
    cC
    cmpt
    #
    cD
    crli
    wbr
    #
    vk
    cB
    wral
    #
    @79
    @63
    wph
    @82
    @42
    wph
    @81
    vk
    cB
    fsumrlim.4
    ralrimiva
    adantr
    @81
    @79
    vk
    @26
    cB
    vk
    @78
    @51
    crli
    vk
    vx
    cA
    @47
    vk
    cA
    nfcv
    @69
    nfmpt
    vk
    crli
    nfcv
    vk
    @26
    cD
    nfcsb1v
    #
    nfbr
    @70
    @80
    @78
    cD
    @51
    crli
    @70
    vx
    cA
    cC
    @47
    @71
    mpteq2dv
    vk
    @26
    cD
    csbeq1a
    #
    breq12d
    rspc
    sylc
    adantr
    syl5eqbrr
    rlimadd
    @44
    @31
    vx
    cA
    @20
    @47
    caddc
    co
    #
    cmpt
    #
    @50
    @43
    @31
    @86
    wceq
    @23
    @43
    vx
    cA
    @30
    @85
    @59
    @30
    @20
    @27
    cC
    vk
    csu
    #
    caddc
    co
    @85
    @59
    @18
    @27
    cC
    @28
    vk
    @43
    @18
    @27
    cin
    c0
    wceq
    #
    @58
    @43
    @40
    @88
    wph
    @40
    @29
    simprl
    @18
    @26
    disjsn
    sylibr
    #
    adantr
    @59
    @28
    eqidd
    @43
    @28
    cfn
    wcel
    #
    @58
    @43
    @5
    @29
    @90
    wph
    @5
    @42
    fsumrlim.2
    adantr
    @62
    cB
    @28
    ssfi
    syl2anc
    #
    adantr
    @59
    @65
    @28
    wcel
    #
    @66
    @61
    @43
    @92
    @66
    @58
    @43
    @28
    cB
    @65
    @62
    sselda
    #
    adantlr
    @68
    syldan
    fsumsplit
    @59
    @87
    @47
    @20
    caddc
    @59
    @87
    @27
    vk
    @7
    cC
    csb
    #
    vw
    csu
    #
    @47
    @27
    cC
    @94
    vk
    vw
    vw
    cC
    nfcv
    vk
    @7
    cC
    nfcsb1v
    vk
    @7
    cC
    csbeq1a
    cbvsumi
    @59
    @60
    @56
    @95
    @47
    wceq
    @64
    @72
    @94
    @47
    vw
    @26
    cB
    vk
    @7
    @26
    cC
    csbeq1
    sumsn
    syl2anc
    syl5eq
    oveq2d
    eqtrd
    mpteq2dva
    adantr
    vx
    vw
    cA
    @85
    @49
    vw
    @85
    nfcv
    vx
    @46
    @48
    caddc
    @76
    vx
    caddc
    nfcv
    @73
    nfov
    @74
    @20
    @46
    @47
    @48
    caddc
    @77
    @75
    oveq12d
    cbvmpt
    syl6eq
    @43
    @32
    @52
    wceq
    @23
    @43
    @32
    @22
    @27
    cD
    vk
    csu
    #
    caddc
    co
    @52
    @43
    @18
    @27
    cD
    @28
    vk
    @89
    @43
    @28
    eqidd
    @91
    @43
    @92
    @66
    cD
    cc
    wcel
    #
    @93
    wph
    @66
    @97
    @42
    @67
    @81
    @97
    fsumrlim.4
    cD
    @80
    rlimcl
    syl
    adantlr
    #
    syldan
    fsumsplit
    @43
    @96
    @51
    @22
    caddc
    @43
    @96
    @27
    vk
    @7
    cD
    csb
    #
    vw
    csu
    #
    @51
    @27
    cD
    @99
    vk
    vw
    vw
    cD
    nfcv
    vk
    @7
    cD
    nfcsb1v
    vk
    @7
    cD
    csbeq1a
    cbvsumi
    @43
    @60
    @51
    cc
    wcel
    #
    @100
    @51
    wceq
    @63
    @43
    @60
    @97
    vk
    cB
    wral
    @101
    @63
    @43
    @97
    vk
    cB
    @98
    ralrimiva
    @97
    @101
    vk
    @26
    cB
    vk
    @51
    cc
    @83
    nfel1
    @70
    cD
    @51
    cc
    @84
    eleq1d
    rspc
    sylc
    @99
    @51
    vw
    @26
    cB
    vk
    @7
    @26
    cD
    csbeq1
    sumsn
    syl2anc
    syl5eq
    oveq2d
    eqtrd
    adantr
    3brtr4d
    ex
    expr
    a2d
    syl5
    expcom
    a2d
    adantl
    findcard2s
    mpcom
    mpi
end
