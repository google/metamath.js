include "cn.mm"
include "cv.mm"
include "cfv.mm"
include "cvoln.mm"
include "cmpt.mm"
include "cli.mm"
include "wbr.mm"
include "cmin.mm"
include "co.mm"
include "cprod.mm"
include "wceq.mm"
include "ciun.mm"
include "c1.mm"
include "vonmea.mm"
include "1zzd.mm"
include "nnuz.mm"
include "cico.mm"
include "cixp.mm"
include "cdm.mm"
include "wcel.mm"
include "wa.mm"
include "cfn.mm"
include "adantr.mm"
include "eqid.mm"
include "cr.mm"
include "wf.mm"
include "cdiv.mm"
include "caddc.mm"
include "ffvelrnda.mm"
include "nnrecre.mm"
include "ad2antlr.mm"
include "readdcld.mm"
include "fmptd.mm"
include "cvv.mm"
include "a1i.mm"
include "mptexd.mm"
include "fvmpt2d.mm"
include "feq1d.mm"
include "mpbird.mm"
include "hoimbl.mm"
include "wss.mm"
include "nfv.mm"
include "cxr.mm"
include "cle.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "mpteq2dv.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "adantl.mm"
include "simpr.mm"
include "peano2nnd.mm"
include "fvmptd.mm"
include "ovexd.mm"
include "1red.mm"
include "nnre.mm"
include "cc0.mm"
include "wne.mm"
include "peano2nn.mm"
include "nnne0.mm"
include "syl.mm"
include "redivcld.mm"
include "eqeltrd.mm"
include "rexrd.mm"
include "ressxr.mm"
include "sseldi.mm"
include "adantlr.mm"
include "clt.mm"
include "ltp1d.mm"
include "nnrp.mm"
include "nnrpd.mm"
include "ltrecd.mm"
include "mpbid.mm"
include "ltled.mm"
include "leadd2dd.mm"
include "breq12d.mm"
include "eqidd.mm"
include "eqled.mm"
include "icossico.mm"
include "syl22anc.mm"
include "ixpssixp.mm"
include "elexd.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "oveq1d.mm"
include "ixpeq2dv.mm"
include "wral.mm"
include "ovex.mm"
include "rgenw.mm"
include "ixpexg.mm"
include "ax-mp.mm"
include "sseq12d.mm"
include "vonhoire.mm"
include "cioo.mm"
include "wtru.mm"
include "nftru.mm"
include "ioossico.mm"
include "trud.mm"
include "eqsstrd.mm"
include "fssd.mm"
include "ioovonmbl.mm"
include "syl5eqel.mm"
include "meassre.mm"
include "cmea.mm"
include "crp.mm"
include "rpreccld.mm"
include "ltaddrpd.mm"
include "icossioo.mm"
include "ixpeq2dva.mm"
include "eqtrd.mm"
include "meassle.mm"
include "meaiuninc2.mm"
include "iunhoiioo.mm"
include "iuneq2dv.mm"
include "3eqtr4d.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "breqtrd.mm"
include "crn.mm"
include "cinf.mm"
include "cfl.mm"
include "cuz.mm"
include "eqcomi.mm"
include "wi.mm"
include "eqcom.mm"
include "imbi1i.mm"
include "imbi2i.mm"
include "bitri.mm"
include "mpbi.mm"
include "prodeq2ad.mm"
include "oveq12d.mm"
include "rneqi.mm"
include "infeq1i.mm"
include "oveq2i.mm"
include "fveq2i.mm"
include "oveq1i.mm"
include "vonioolem1.mm"
include "eqbrtrd.mm"
include "climuni.mm"
include "syl2anc.mm"

theorem vonioolem2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  let vn: setvar n
  let cI: class I
  let cX: class X
  let vj: setvar j
  let vm: setvar m
  let vx: setvar x
  assume vonioolem2.x: |- ( ph -> X e. Fin )
  assume vonioolem2.a: |- ( ph -> A : X --> RR )
  assume vonioolem2.b: |- ( ph -> B : X --> RR )
  assume vonioolem2.n: |- ( ph -> X =/= (/) )
  assume vonioolem2.t: |- ( ( ph /\ k e. X ) -> ( A ` k ) < ( B ` k ) )
  assume vonioolem2.i: |- I = X_ k e. X ( ( A ` k ) (,) ( B ` k ) )
  assume vonioolem2.c: |- C = ( n e. NN |-> ( k e. X |-> ( ( A ` k ) + ( 1 / n ) ) ) )
  assume vonioolem2.d: |- D = ( n e. NN |-> X_ k e. X ( ( ( C ` n ) ` k ) [,) ( B ` k ) ) )

  disjoint A k
  disjoint A n
  disjoint k n
  disjoint B k
  disjoint B n
  disjoint C k
  disjoint C n
  disjoint D n
  disjoint I n
  disjoint X k
  disjoint X n
  disjoint k ph
  disjoint n ph
  disjoint A j
  disjoint j k
  disjoint j n
  disjoint A m
  disjoint k m
  disjoint m n
  disjoint B j
  disjoint B m
  disjoint C m
  disjoint D m
  disjoint X j
  disjoint X m
  disjoint m ph
  disjoint k x
  assert |- ( ph -> ( ( voln ` X ) ` I ) = prod_ k e. X ( ( B ` k ) - ( A ` k ) ) )

  proof
    wph
    vn
    cn
    vn
    cv
    #
    cD
    cfv
    #
    cX
    cvoln
    cfv
    #
    cfv
    #
    cmpt
    #
    cI
    @2
    cfv
    #
    cli
    wbr
    @4
    cX
    vk
    cv
    #
    cB
    cfv
    #
    @6
    cA
    cfv
    #
    cmin
    co
    #
    vk
    cprod
    #
    cli
    wbr
    @5
    @10
    wceq
    wph
    @4
    vn
    cn
    @1
    ciun
    #
    @2
    cfv
    #
    @5
    cli
    wph
    @5
    @4
    vn
    cD
    @2
    c1
    cn
    wph
    cX
    vonioolem2.x
    vonmea
    #
    wph
    1zzd
    nnuz
    wph
    vn
    cn
    vk
    cX
    @6
    @0
    cC
    cfv
    #
    cfv
    #
    @7
    cico
    co
    #
    cixp
    #
    @2
    cdm
    #
    cD
    wph
    @0
    cn
    wcel
    #
    wa
    #
    @14
    cB
    @18
    vk
    cX
    wph
    cX
    cfn
    wcel
    @19
    vonioolem2.x
    adantr
    #
    @18
    eqid
    #
    @20
    cX
    cr
    @14
    wf
    cX
    cr
    vk
    cX
    @8
    c1
    @0
    cdiv
    co
    #
    caddc
    co
    #
    cmpt
    #
    wf
    @20
    vk
    cX
    @24
    cr
    @25
    @20
    @6
    cX
    wcel
    #
    wa
    #
    @8
    @23
    @20
    cX
    cr
    @6
    cA
    wph
    cX
    cr
    cA
    wf
    @19
    vonioolem2.a
    adantr
    ffvelrnda
    #
    @19
    @23
    cr
    wcel
    wph
    @26
    @0
    nnrecre
    #
    ad2antlr
    #
    readdcld
    @25
    eqid
    fmptd
    @20
    cX
    cr
    @14
    @25
    wph
    vn
    cn
    @25
    cC
    cvv
    cC
    vn
    cn
    @25
    cmpt
    #
    wceq
    wph
    vonioolem2.c
    a1i
    wph
    @25
    cvv
    wcel
    @19
    wph
    vk
    cX
    @24
    cfn
    vonioolem2.x
    mptexd
    adantr
    fvmpt2d
    #
    feq1d
    mpbird
    wph
    cX
    cr
    cB
    wf
    @19
    vonioolem2.b
    adantr
    hoimbl
    #
    vonioolem2.d
    fmptd
    @20
    @1
    @0
    c1
    caddc
    co
    #
    cD
    cfv
    #
    wss
    @17
    vk
    cX
    @6
    @34
    cC
    cfv
    #
    cfv
    #
    @7
    cico
    co
    #
    cixp
    #
    wss
    @20
    vk
    cX
    @16
    @38
    @20
    vk
    nfv
    #
    @27
    @37
    cxr
    wcel
    @7
    cxr
    wcel
    #
    @37
    @15
    cle
    wbr
    #
    @7
    @7
    cle
    wbr
    #
    @16
    @38
    wss
    @27
    @37
    @27
    @37
    @8
    c1
    @34
    cdiv
    co
    #
    caddc
    co
    #
    cr
    @20
    vk
    cX
    @45
    @36
    cvv
    @20
    vm
    @34
    vk
    cX
    @8
    c1
    vm
    cv
    #
    cdiv
    co
    #
    caddc
    co
    #
    cmpt
    #
    vk
    cX
    @45
    cmpt
    #
    cn
    cC
    cvv
    cC
    vm
    cn
    @49
    cmpt
    #
    wceq
    @20
    cC
    @31
    @51
    vonioolem2.c
    vn
    vm
    cn
    @25
    @49
    @0
    @46
    wceq
    #
    vk
    cX
    @24
    @48
    @52
    @23
    @47
    @8
    caddc
    @0
    @46
    c1
    cdiv
    oveq2
    oveq2d
    mpteq2dv
    cbvmptv
    eqtri
    a1i
    @46
    @34
    wceq
    #
    @49
    @50
    wceq
    @20
    @53
    vk
    cX
    @48
    @45
    @53
    @47
    @44
    @8
    caddc
    @46
    @34
    c1
    cdiv
    oveq2
    oveq2d
    mpteq2dv
    adantl
    @20
    @0
    wph
    @19
    simpr
    peano2nnd
    #
    @20
    vk
    cX
    @45
    cfn
    @21
    mptexd
    fvmptd
    @27
    @8
    @44
    caddc
    ovexd
    fvmpt2d
    #
    @27
    @8
    @44
    @28
    @19
    @44
    cr
    wcel
    wph
    @26
    @19
    c1
    @34
    @19
    1red
    #
    @19
    @0
    c1
    @0
    nnre
    #
    @56
    readdcld
    @19
    @34
    cn
    wcel
    @34
    cc0
    wne
    @0
    peano2nn
    #
    @34
    nnne0
    syl
    redivcld
    #
    ad2antlr
    #
    readdcld
    eqeltrd
    rexrd
    wph
    @26
    @41
    @19
    wph
    @26
    wa
    #
    cr
    cxr
    @7
    ressxr
    wph
    cX
    cr
    @6
    cB
    vonioolem2.b
    ffvelrnda
    #
    sseldi
    #
    adantlr
    #
    @27
    @42
    @45
    @24
    cle
    wbr
    @27
    @44
    @23
    @8
    @60
    @30
    @28
    @19
    @44
    @23
    cle
    wbr
    wph
    @26
    @19
    @44
    @23
    @59
    @29
    @19
    @0
    @34
    clt
    wbr
    @44
    @23
    clt
    wbr
    @19
    @0
    @57
    ltp1d
    @19
    @0
    @34
    @0
    nnrp
    #
    @19
    @34
    @58
    nnrpd
    ltrecd
    mpbid
    ltled
    ad2antlr
    leadd2dd
    @27
    @37
    @45
    @15
    @24
    cle
    @55
    @20
    vk
    cX
    @24
    @14
    cvv
    @32
    @27
    @8
    @23
    caddc
    ovexd
    fvmpt2d
    #
    breq12d
    mpbird
    @27
    @7
    @7
    wph
    @26
    @7
    cr
    wcel
    @19
    @62
    adantlr
    @27
    @7
    eqidd
    eqled
    #
    @37
    @7
    @15
    @7
    icossico
    syl22anc
    ixpssixp
    @20
    @1
    @17
    @35
    @39
    wph
    vn
    cn
    @17
    cD
    cvv
    cD
    vn
    cn
    @17
    cmpt
    #
    wceq
    wph
    vonioolem2.d
    a1i
    @20
    @17
    @18
    @33
    elexd
    fvmpt2d
    #
    @20
    vm
    @34
    vk
    cX
    @6
    @46
    cC
    cfv
    #
    cfv
    #
    @7
    cico
    co
    #
    cixp
    #
    @39
    cn
    cD
    cvv
    cD
    vm
    cn
    @73
    cmpt
    #
    wceq
    @20
    cD
    @68
    @74
    vonioolem2.d
    vn
    vm
    cn
    @17
    @73
    @52
    vk
    cX
    @16
    @72
    @52
    @15
    @71
    @7
    cico
    @52
    @6
    @14
    @70
    @0
    @46
    cC
    fveq2
    fveq1d
    #
    oveq1d
    ixpeq2dv
    cbvmptv
    eqtri
    a1i
    @53
    @73
    @39
    wceq
    @20
    @53
    vk
    cX
    @72
    @38
    @53
    @71
    @37
    @7
    cico
    @53
    @6
    @70
    @36
    @46
    @34
    cC
    fveq2
    fveq1d
    oveq1d
    ixpeq2dv
    adantl
    @54
    @39
    cvv
    wcel
    #
    @20
    @38
    cvv
    wcel
    #
    vk
    cX
    wral
    @76
    @77
    vk
    cX
    @37
    @7
    cico
    ovex
    rgenw
    vk
    cX
    @38
    cvv
    ixpexg
    ax-mp
    a1i
    fvmptd
    sseq12d
    mpbird
    wph
    vk
    cX
    @8
    @7
    cico
    co
    #
    cixp
    #
    cI
    @2
    @13
    wph
    cA
    cB
    @18
    vk
    cX
    vonioolem2.x
    @22
    vonioolem2.a
    vonioolem2.b
    hoimbl
    wph
    @8
    @7
    vk
    cX
    wph
    vk
    nfv
    #
    vonioolem2.x
    wph
    cX
    cr
    @6
    cA
    vonioolem2.a
    ffvelrnda
    #
    @62
    vonhoire
    wph
    cI
    vk
    cX
    @8
    @7
    cioo
    co
    #
    cixp
    #
    @79
    cI
    @83
    wceq
    #
    wph
    vonioolem2.i
    a1i
    #
    @83
    @79
    wss
    #
    wph
    @86
    wtru
    vk
    cX
    @82
    @78
    vk
    nftru
    @82
    @78
    wss
    wtru
    @26
    wa
    @8
    @7
    ioossico
    a1i
    ixpssixp
    trud
    a1i
    eqsstrd
    wph
    cI
    @83
    @18
    vonioolem2.i
    wph
    cA
    cB
    @18
    vk
    cX
    vonioolem2.x
    @22
    wph
    cX
    cr
    cxr
    cA
    vonioolem2.a
    cr
    cxr
    wss
    wph
    ressxr
    a1i
    #
    fssd
    wph
    cX
    cr
    cxr
    cB
    vonioolem2.b
    @87
    fssd
    ioovonmbl
    syl5eqel
    #
    meassre
    @20
    @1
    cI
    @18
    @2
    wph
    @2
    cmea
    wcel
    @19
    @13
    adantr
    @22
    @20
    @1
    @17
    @18
    @69
    @33
    eqeltrd
    wph
    cI
    @18
    wcel
    @19
    @88
    adantr
    @20
    @1
    cI
    wss
    vk
    cX
    @24
    @7
    cico
    co
    #
    cixp
    #
    @83
    wss
    @20
    vk
    cX
    @89
    @82
    @40
    @27
    @8
    cxr
    wcel
    #
    @41
    @8
    @24
    clt
    wbr
    @43
    @89
    @82
    wss
    wph
    @26
    @91
    @19
    @61
    cr
    cxr
    @8
    ressxr
    @81
    sseldi
    adantlr
    @64
    @27
    @8
    @23
    @28
    @19
    @23
    crp
    wcel
    wph
    @26
    @19
    @0
    @65
    rpreccld
    ad2antlr
    ltaddrpd
    @67
    @8
    @7
    @24
    @7
    icossioo
    syl22anc
    ixpssixp
    @20
    @1
    @90
    cI
    @83
    @20
    @1
    @17
    @90
    @69
    @20
    vk
    cX
    @16
    @89
    @27
    @15
    @24
    @7
    cico
    @66
    oveq1d
    ixpeq2dva
    eqtrd
    #
    @84
    @20
    vonioolem2.i
    a1i
    sseq12d
    mpbird
    meassle
    @4
    eqid
    meaiuninc2
    wph
    @5
    @12
    wph
    cI
    @11
    @2
    wph
    @11
    cI
    wph
    vn
    cn
    @90
    ciun
    @83
    @11
    cI
    wph
    @8
    @7
    vk
    vn
    cX
    @80
    vonioolem2.x
    @81
    @63
    iunhoiioo
    wph
    vn
    cn
    @1
    @90
    @92
    iuneq2dv
    @85
    3eqtr4d
    eqcomd
    fveq2d
    eqcomd
    breqtrd
    wph
    @4
    vm
    cn
    @46
    cD
    cfv
    #
    @2
    cfv
    #
    cmpt
    #
    @10
    cli
    @4
    @95
    wceq
    wph
    vn
    vm
    cn
    @3
    @94
    @52
    @1
    @93
    @2
    @0
    @46
    cD
    fveq2
    fveq2d
    cbvmptv
    #
    a1i
    wph
    cA
    cB
    cC
    cD
    @95
    vm
    cn
    cX
    @7
    @71
    cmin
    co
    #
    vk
    cprod
    #
    cmpt
    vk
    vn
    vk
    cX
    @9
    cmpt
    #
    crn
    #
    cr
    clt
    cinf
    #
    c1
    @101
    cdiv
    co
    #
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    cX
    c1
    vj
    cX
    vj
    cv
    #
    cB
    cfv
    #
    @105
    cA
    cfv
    #
    cmin
    co
    #
    cmpt
    #
    crn
    #
    cr
    clt
    cinf
    #
    cdiv
    co
    #
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    cuz
    cfv
    vonioolem2.x
    vonioolem2.a
    vonioolem2.b
    vonioolem2.n
    vonioolem2.t
    vonioolem2.c
    vonioolem2.d
    @4
    @95
    @96
    eqcomi
    vm
    vn
    cn
    @98
    cX
    @7
    @15
    cmin
    co
    #
    vk
    cprod
    @46
    @0
    wceq
    #
    cX
    @97
    @115
    vk
    @116
    @71
    @15
    @7
    cmin
    @52
    @15
    @71
    wceq
    #
    wi
    #
    @116
    @71
    @15
    wceq
    #
    wi
    #
    @75
    @118
    @116
    @117
    wi
    @120
    @52
    @116
    @117
    @0
    @46
    eqcom
    imbi1i
    @117
    @119
    @116
    @15
    @71
    eqcom
    imbi2i
    bitri
    mpbi
    oveq2d
    prodeq2ad
    cbvmptv
    @101
    eqid
    @104
    eqid
    @114
    @104
    cuz
    @113
    @103
    c1
    caddc
    @112
    @102
    cfl
    @111
    @101
    c1
    cdiv
    cr
    @110
    @100
    clt
    @109
    @99
    vj
    vk
    cX
    @108
    @9
    @105
    @6
    wceq
    @106
    @7
    @107
    @8
    cmin
    @105
    @6
    cB
    fveq2
    @105
    @6
    cA
    fveq2
    oveq12d
    cbvmptv
    rneqi
    infeq1i
    oveq2i
    fveq2i
    oveq1i
    fveq2i
    vonioolem1
    eqbrtrd
    @5
    @10
    @4
    climuni
    syl2anc
end
