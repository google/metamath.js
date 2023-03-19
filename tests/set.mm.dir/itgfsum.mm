include "wss.mm"
include "csu.mm"
include "cmpt.mm"
include "cibl.mm"
include "wcel.mm"
include "citg.mm"
include "wceq.mm"
include "wa.mm"
include "ssid.mm"
include "cfn.mm"
include "wi.mm"
include "cv.mm"
include "c0.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "cun.mm"
include "sseq1.mm"
include "sumeq1.mm"
include "sum0.mm"
include "syl6eq.mm"
include "mpteq2dv.mm"
include "fconstmpt.mm"
include "syl6eqr.mm"
include "eleq1d.mm"
include "anbi1d.mm"
include "itgz.mm"
include "adantr.mm"
include "itgeq2dv.mm"
include "3eqtr4a.mm"
include "biantrud.mm"
include "bitr4d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "weq.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "cvol.mm"
include "cdm.mm"
include "ibl0.mm"
include "syl.mm"
include "a1d.mm"
include "wn.mm"
include "ssun1.mm"
include "sstr.mm"
include "mpan.mm"
include "imim1i.mm"
include "csb.mm"
include "caddc.mm"
include "co.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbvsumi.mm"
include "cin.mm"
include "simprl.mm"
include "disjsn.mm"
include "sylibr.mm"
include "eqidd.mm"
include "simprr.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "cc.mm"
include "simplrr.mm"
include "sselda.mm"
include "wral.mm"
include "cmbf.mm"
include "iblmbf.mm"
include "anass1rs.mm"
include "mbfmptcl.mm"
include "an32s.mm"
include "ralrimiva.mm"
include "adantlr.mm"
include "nfel1.mm"
include "cbvral.mm"
include "sylib.mm"
include "r19.21bi.mm"
include "syldan.mm"
include "fsumsplit.mm"
include "cvv.mm"
include "vex.mm"
include "unssbd.mm"
include "snss.mm"
include "csbeq1.mm"
include "rspcv.mm"
include "sylc.mm"
include "sumsn.mm"
include "sylancr.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "syl5eq.mm"
include "mpteq2dva.mm"
include "nfov.mm"
include "oveq12d.mm"
include "cbvmpt.mm"
include "sumex.mm"
include "csbex.mm"
include "a1i.mm"
include "mpteq2i.mm"
include "eqtri.mm"
include "syl5eqelr.mm"
include "elex.mm"
include "nfv.mm"
include "nfmpt.mm"
include "ibladd.mm"
include "eqeltrd.mm"
include "itgadd.mm"
include "cbvitg.mm"
include "oveq12i.mm"
include "3eqtr4g.mm"
include "itgcl.mm"
include "itgeq2.mm"
include "mprg.mm"
include "nfitg.mm"
include "3eqtr3g.mm"
include "eqcomd.mm"
include "eqtr4d.mm"
include "3eqtr4d.mm"
include "jca.mm"
include "ex.mm"
include "expr.mm"
include "a2d.mm"
include "syl5.mm"
include "expcom.mm"
include "adantl.mm"
include "findcard2s.mm"
include "mpcom.mm"
include "mpi.mm"

theorem itgfsum
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cV: class V
  let vm: setvar m
  let vt: setvar t
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume itgfsum.1: |- ( ph -> A e. dom vol )
  assume itgfsum.2: |- ( ph -> B e. Fin )
  assume itgfsum.3: |- ( ( ph /\ ( x e. A /\ k e. B ) ) -> C e. V )
  assume itgfsum.4: |- ( ( ph /\ k e. B ) -> ( x e. A |-> C ) e. L^1 )

  disjoint k x
  disjoint A k
  disjoint A x
  disjoint B k
  disjoint B x
  disjoint k ph
  disjoint ph x
  disjoint k m
  disjoint k t
  disjoint k w
  disjoint k y
  disjoint k z
  disjoint m t
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B m
  disjoint B t
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint m ph
  disjoint ph t
  disjoint ph w
  disjoint ph y
  disjoint ph z
  disjoint C m
  disjoint C t
  disjoint C w
  disjoint C y
  disjoint C z
  assert |- ( ph -> ( ( x e. A |-> sum_ k e. B C ) e. L^1 /\ S. A sum_ k e. B C _d x = sum_ k e. B S. A C _d x ) )

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
    cibl
    wcel
    #
    vx
    cA
    @1
    citg
    #
    cB
    vx
    cA
    cC
    citg
    #
    vk
    csu
    #
    wceq
    #
    wa
    #
    cB
    ssid
    cB
    cfn
    wcel
    #
    wph
    @0
    @8
    wi
    #
    itgfsum.2
    wph
    vt
    cv
    #
    cB
    wss
    #
    vx
    cA
    @11
    cC
    vk
    csu
    #
    cmpt
    #
    cibl
    wcel
    #
    vx
    cA
    @13
    citg
    #
    @11
    @5
    vk
    csu
    #
    wceq
    #
    wa
    #
    wi
    #
    wi
    wph
    c0
    cB
    wss
    #
    cA
    cc0
    csn
    cxp
    #
    cibl
    wcel
    #
    wi
    #
    wi
    wph
    vw
    cv
    #
    cB
    wss
    #
    vx
    cA
    @25
    cC
    vk
    csu
    #
    cmpt
    #
    cibl
    wcel
    #
    vx
    cA
    @27
    citg
    #
    @25
    @5
    vk
    csu
    #
    wceq
    #
    wa
    #
    wi
    #
    wi
    wph
    @25
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
    @37
    cC
    vk
    csu
    #
    cmpt
    #
    cibl
    wcel
    #
    vx
    cA
    @39
    citg
    #
    @37
    @5
    vk
    csu
    #
    wceq
    #
    wa
    #
    wi
    #
    wi
    wph
    @10
    wi
    vt
    vw
    vz
    cB
    @11
    c0
    wceq
    #
    @20
    @24
    wph
    @47
    @12
    @21
    @19
    @23
    @11
    c0
    cB
    sseq1
    @47
    @19
    @23
    @18
    wa
    @23
    @47
    @15
    @23
    @18
    @47
    @14
    @22
    cibl
    @47
    @14
    vx
    cA
    cc0
    cmpt
    @22
    @47
    vx
    cA
    @13
    cc0
    @47
    @13
    c0
    cC
    vk
    csu
    cc0
    @11
    c0
    cC
    vk
    sumeq1
    cC
    vk
    sum0
    syl6eq
    #
    mpteq2dv
    vx
    cA
    cc0
    fconstmpt
    syl6eqr
    eleq1d
    anbi1d
    @47
    @18
    @23
    @47
    vx
    cA
    cc0
    citg
    cc0
    @16
    @17
    vx
    cA
    itgz
    @47
    vx
    cA
    @13
    cc0
    @47
    @13
    cc0
    wceq
    vx
    cv
    cA
    wcel
    #
    @48
    adantr
    itgeq2dv
    @47
    @17
    c0
    @5
    vk
    csu
    cc0
    @11
    c0
    @5
    vk
    sumeq1
    @5
    vk
    sum0
    syl6eq
    3eqtr4a
    biantrud
    bitr4d
    imbi12d
    imbi2d
    vt
    vw
    weq
    #
    @20
    @34
    wph
    @50
    @12
    @26
    @19
    @33
    @11
    @25
    cB
    sseq1
    @50
    @15
    @29
    @18
    @32
    @50
    @14
    @28
    cibl
    @50
    vx
    cA
    @13
    @27
    @11
    @25
    cC
    vk
    sumeq1
    #
    mpteq2dv
    eleq1d
    @50
    @16
    @30
    @17
    @31
    @50
    vx
    cA
    @13
    @27
    @50
    @13
    @27
    wceq
    @49
    @51
    adantr
    itgeq2dv
    @11
    @25
    @5
    vk
    sumeq1
    eqeq12d
    anbi12d
    imbi12d
    imbi2d
    @11
    @37
    wceq
    #
    @20
    @46
    wph
    @52
    @12
    @38
    @19
    @45
    @11
    @37
    cB
    sseq1
    @52
    @15
    @41
    @18
    @44
    @52
    @14
    @40
    cibl
    @52
    vx
    cA
    @13
    @39
    @11
    @37
    cC
    vk
    sumeq1
    #
    mpteq2dv
    eleq1d
    @52
    @16
    @42
    @17
    @43
    @52
    vx
    cA
    @13
    @39
    @52
    @13
    @39
    wceq
    @49
    @53
    adantr
    itgeq2dv
    @11
    @37
    @5
    vk
    sumeq1
    eqeq12d
    anbi12d
    imbi12d
    imbi2d
    @11
    cB
    wceq
    #
    @20
    @10
    wph
    @54
    @12
    @0
    @19
    @8
    @11
    cB
    cB
    sseq1
    @54
    @15
    @3
    @18
    @7
    @54
    @14
    @2
    cibl
    @54
    vx
    cA
    @13
    @1
    @11
    cB
    cC
    vk
    sumeq1
    #
    mpteq2dv
    eleq1d
    @54
    @16
    @4
    @17
    @6
    @54
    vx
    cA
    @13
    @1
    @54
    @13
    @1
    wceq
    @49
    @55
    adantr
    itgeq2dv
    @11
    cB
    @5
    vk
    sumeq1
    eqeq12d
    anbi12d
    imbi12d
    imbi2d
    wph
    @23
    @21
    wph
    cA
    cvol
    cdm
    wcel
    @23
    itgfsum.1
    cA
    ibl0
    syl
    a1d
    @25
    cfn
    wcel
    #
    @35
    @25
    wcel
    wn
    #
    wa
    wph
    @34
    @46
    @57
    wph
    @34
    @46
    wi
    #
    wi
    @56
    wph
    @57
    @58
    @34
    @38
    @33
    wi
    wph
    @57
    wa
    #
    @46
    @38
    @26
    @33
    @25
    @37
    wss
    @38
    @26
    @25
    @36
    ssun1
    @25
    @37
    cB
    sstr
    mpan
    imim1i
    @59
    @38
    @33
    @45
    wph
    @57
    @38
    @33
    @45
    wi
    wph
    @57
    @38
    wa
    #
    wa
    #
    @33
    @45
    @61
    @33
    wa
    #
    @41
    @44
    @62
    @40
    vy
    cA
    vx
    vy
    cv
    #
    @25
    vk
    vm
    cv
    #
    cC
    csb
    #
    vm
    csu
    #
    csb
    #
    vx
    @63
    vk
    @35
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
    cibl
    @61
    @40
    @71
    wceq
    @33
    @61
    @40
    vx
    cA
    @66
    @68
    caddc
    co
    #
    cmpt
    @71
    @61
    vx
    cA
    @39
    @72
    @61
    @49
    wa
    #
    @39
    @37
    @65
    vm
    csu
    #
    @72
    @37
    cC
    @65
    vk
    vm
    vm
    cC
    nfcv
    #
    vk
    @64
    cC
    nfcsb1v
    #
    vk
    @64
    cC
    csbeq1a
    #
    cbvsumi
    #
    @73
    @74
    @66
    @36
    @65
    vm
    csu
    #
    caddc
    co
    @72
    @73
    @25
    @36
    @65
    @37
    vm
    @61
    @25
    @36
    cin
    c0
    wceq
    #
    @49
    @61
    @57
    @80
    wph
    @57
    @38
    simprl
    @25
    @35
    disjsn
    sylibr
    #
    adantr
    @73
    @37
    eqidd
    @61
    @37
    cfn
    wcel
    #
    @49
    @61
    @9
    @38
    @82
    wph
    @9
    @60
    itgfsum.2
    adantr
    wph
    @57
    @38
    simprr
    #
    cB
    @37
    ssfi
    syl2anc
    #
    adantr
    @73
    @64
    @37
    wcel
    #
    @64
    cB
    wcel
    #
    @65
    cc
    wcel
    #
    @73
    @37
    cB
    @64
    wph
    @57
    @38
    @49
    simplrr
    sselda
    @73
    @87
    vm
    cB
    @73
    cC
    cc
    wcel
    #
    vk
    cB
    wral
    #
    @87
    vm
    cB
    wral
    #
    wph
    @49
    @89
    @60
    wph
    @49
    wa
    @88
    vk
    cB
    wph
    vk
    cv
    cB
    wcel
    #
    @49
    @88
    wph
    @91
    wa
    #
    vx
    cA
    cC
    cV
    @92
    vx
    cA
    cC
    cmpt
    #
    cibl
    wcel
    #
    @93
    cmbf
    wcel
    itgfsum.4
    @93
    iblmbf
    syl
    wph
    @49
    @91
    cC
    cV
    wcel
    itgfsum.3
    anass1rs
    mbfmptcl
    an32s
    ralrimiva
    adantlr
    @88
    @87
    vk
    vm
    cB
    vm
    cC
    cc
    @75
    nfel1
    vk
    @65
    cc
    @76
    nfel1
    vk
    vm
    weq
    #
    cC
    @65
    cc
    @77
    eleq1d
    cbvral
    sylib
    #
    r19.21bi
    #
    syldan
    fsumsplit
    @73
    @79
    @68
    @66
    caddc
    @73
    @35
    cvv
    wcel
    #
    @68
    cc
    wcel
    #
    @79
    @68
    wceq
    vz
    vex
    #
    @73
    @35
    cB
    wcel
    #
    @90
    @99
    @61
    @101
    @49
    @61
    @36
    cB
    wss
    @101
    @61
    @25
    @36
    cB
    @83
    unssbd
    @35
    cB
    @100
    snss
    sylibr
    #
    adantr
    @96
    @87
    @99
    vm
    @35
    cB
    vm
    vz
    weq
    #
    @65
    @68
    cc
    vk
    @64
    @35
    cC
    csbeq1
    #
    eleq1d
    rspcv
    sylc
    #
    @65
    @68
    vm
    @35
    cvv
    @104
    sumsn
    sylancr
    oveq2d
    eqtrd
    #
    syl5eq
    mpteq2dva
    vx
    vy
    cA
    @72
    @70
    vy
    @72
    nfcv
    #
    vx
    @67
    @69
    caddc
    vx
    @63
    @66
    nfcsb1v
    #
    vx
    caddc
    nfcv
    vx
    @63
    @68
    nfcsb1v
    #
    nfov
    #
    vx
    vy
    weq
    #
    @66
    @67
    @68
    @69
    caddc
    vx
    @63
    @66
    csbeq1a
    #
    vx
    @63
    @68
    csbeq1a
    #
    oveq12d
    #
    cbvmpt
    syl6eq
    adantr
    @62
    vy
    cA
    @67
    @69
    cvv
    @67
    cvv
    wcel
    @62
    @63
    cA
    wcel
    wa
    vx
    @63
    @66
    @25
    @65
    vm
    sumex
    csbex
    a1i
    #
    @62
    vy
    cA
    @67
    cmpt
    #
    @28
    cibl
    @28
    vx
    cA
    @66
    cmpt
    @116
    vx
    cA
    @27
    @66
    @25
    cC
    @65
    vk
    vm
    @75
    @76
    @77
    cbvsumi
    #
    mpteq2i
    vx
    vy
    cA
    @66
    @67
    vy
    @66
    nfcv
    #
    @108
    @112
    cbvmpt
    eqtri
    @61
    @29
    @32
    simprl
    syl5eqelr
    #
    @62
    @69
    cvv
    wcel
    #
    vy
    cA
    @62
    @68
    cvv
    wcel
    #
    vx
    cA
    wral
    #
    @120
    vy
    cA
    wral
    @61
    @122
    @33
    @61
    @121
    vx
    cA
    @73
    @99
    @121
    @105
    @68
    cc
    elex
    syl
    ralrimiva
    adantr
    @121
    @120
    vx
    vy
    cA
    @121
    vy
    nfv
    vx
    @69
    cvv
    @109
    nfel1
    @111
    @68
    @69
    cvv
    @113
    eleq1d
    cbvral
    sylib
    r19.21bi
    #
    @61
    vy
    cA
    @69
    cmpt
    #
    cibl
    wcel
    @33
    @61
    @124
    vx
    cA
    @68
    cmpt
    #
    cibl
    vx
    vy
    cA
    @68
    @69
    vy
    @68
    nfcv
    #
    @109
    @113
    cbvmpt
    @61
    @101
    vx
    cA
    @65
    cmpt
    #
    cibl
    wcel
    #
    vm
    cB
    wral
    #
    @125
    cibl
    wcel
    #
    @102
    wph
    @129
    @60
    wph
    @94
    vk
    cB
    wral
    @129
    wph
    @94
    vk
    cB
    itgfsum.4
    ralrimiva
    @94
    @128
    vk
    vm
    cB
    @94
    vm
    nfv
    vk
    @127
    cibl
    vk
    vx
    cA
    @65
    vk
    cA
    nfcv
    #
    @76
    nfmpt
    nfel1
    @95
    @93
    @127
    cibl
    @95
    vx
    cA
    cC
    @65
    @77
    mpteq2dv
    eleq1d
    cbvral
    sylib
    adantr
    #
    @128
    @130
    vm
    @35
    cB
    @103
    @127
    @125
    cibl
    @103
    vx
    cA
    @65
    @68
    @104
    mpteq2dv
    eleq1d
    rspcv
    sylc
    #
    syl5eqelr
    adantr
    #
    ibladd
    eqeltrd
    @62
    vx
    cA
    @74
    citg
    #
    @37
    vx
    cA
    @65
    citg
    #
    vm
    csu
    #
    @42
    @43
    @62
    vx
    cA
    @72
    citg
    #
    vx
    cA
    @66
    citg
    #
    vx
    cA
    @68
    citg
    #
    caddc
    co
    #
    @135
    @137
    @62
    vy
    cA
    @70
    citg
    vy
    cA
    @67
    citg
    #
    vy
    cA
    @69
    citg
    #
    caddc
    co
    @138
    @141
    @62
    vy
    cA
    @67
    @69
    cvv
    @115
    @119
    @123
    @134
    itgadd
    vx
    vy
    cA
    @72
    @70
    @114
    @107
    @110
    cbvitg
    @139
    @142
    @140
    @143
    caddc
    vx
    vy
    cA
    @66
    @67
    @112
    @118
    @108
    cbvitg
    vx
    vy
    cA
    @68
    @69
    @113
    @126
    @109
    cbvitg
    oveq12i
    3eqtr4g
    @61
    @135
    @138
    wceq
    @33
    @61
    vx
    cA
    @74
    @72
    @106
    itgeq2dv
    adantr
    @62
    @137
    @25
    @136
    vm
    csu
    #
    @36
    @136
    vm
    csu
    #
    caddc
    co
    #
    @141
    @61
    @137
    @146
    wceq
    @33
    @61
    @25
    @36
    @136
    @37
    vm
    @81
    @61
    @37
    eqidd
    @84
    @61
    @85
    @86
    @136
    cc
    wcel
    @61
    @37
    cB
    @64
    @83
    sselda
    @61
    @86
    wa
    vx
    cA
    @65
    cc
    @61
    @49
    @86
    @87
    @97
    an32s
    @61
    @128
    vm
    cB
    @132
    r19.21bi
    itgcl
    syldan
    fsumsplit
    adantr
    @62
    @139
    @144
    @140
    @145
    caddc
    @62
    @30
    @31
    @139
    @144
    @61
    @29
    @32
    simprr
    @27
    @66
    wceq
    #
    @30
    @139
    wceq
    vx
    cA
    vx
    cA
    @27
    @66
    itgeq2
    @147
    @49
    @117
    a1i
    mprg
    @25
    @5
    @136
    vk
    vm
    vm
    @5
    nfcv
    #
    vx
    vk
    cA
    @65
    @131
    @76
    nfitg
    #
    @95
    vx
    cA
    cC
    @65
    @95
    cC
    @65
    wceq
    @49
    @77
    adantr
    itgeq2dv
    #
    cbvsumi
    3eqtr3g
    @62
    @145
    @140
    @62
    @98
    @140
    cc
    wcel
    #
    @145
    @140
    wceq
    @100
    @61
    @151
    @33
    @61
    vx
    cA
    @68
    cc
    @105
    @133
    itgcl
    adantr
    @136
    @140
    vm
    @35
    cvv
    @103
    vx
    cA
    @65
    @68
    @103
    @65
    @68
    wceq
    @49
    @104
    adantr
    itgeq2dv
    sumsn
    sylancr
    eqcomd
    oveq12d
    eqtr4d
    3eqtr4d
    @39
    @74
    wceq
    #
    @42
    @135
    wceq
    vx
    cA
    vx
    cA
    @39
    @74
    itgeq2
    @152
    @49
    @78
    a1i
    mprg
    @37
    @5
    @136
    vk
    vm
    @148
    @149
    @150
    cbvsumi
    3eqtr4g
    jca
    ex
    expr
    a2d
    syl5
    expcom
    adantl
    a2d
    findcard2s
    mpcom
    mpi
end
