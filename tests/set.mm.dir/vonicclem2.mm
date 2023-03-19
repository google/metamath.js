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
include "ciin.mm"
include "c1.mm"
include "nfv.mm"
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
include "adantlr.mm"
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
include "cxr.mm"
include "cle.mm"
include "ressxr.mm"
include "sseldi.mm"
include "ovexd.mm"
include "eqeltrd.mm"
include "rexrd.mm"
include "leidd.mm"
include "1red.mm"
include "nnre.mm"
include "cc0.mm"
include "wne.mm"
include "peano2nn.mm"
include "nnne0.mm"
include "syl.mm"
include "redivcld.mm"
include "clt.mm"
include "ltp1d.mm"
include "nnrp.mm"
include "nnrpd.mm"
include "ltrecd.mm"
include "mpbid.mm"
include "ltled.mm"
include "leadd2dd.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "mpteq2dv.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "adantl.mm"
include "simpr.mm"
include "peano2nnd.mm"
include "fvmptd.mm"
include "breq12d.mm"
include "icossico.mm"
include "syl22anc.mm"
include "ixpssixp.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "ixpeq2dv.mm"
include "wral.mm"
include "ovex.mm"
include "rgenw.mm"
include "ixpexg.mm"
include "ax-mp.mm"
include "elexd.mm"
include "sseq12d.mm"
include "cuz.mm"
include "1nn.mm"
include "eleqtri.mm"
include "fveq2d.mm"
include "simpl.mm"
include "wi.mm"
include "elexi.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "anbi1d.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "vtocl.mm"
include "syl21anc.mm"
include "vonhoire.mm"
include "meaiininc.mm"
include "cicc.mm"
include "iinhoiicc.mm"
include "ixpeq2dva.mm"
include "eqtrd.mm"
include "iineq2dv.mm"
include "3eqtr4d.mm"
include "eqcomd.mm"
include "breqtrd.mm"
include "eqcomi.mm"
include "vonicclem1.mm"
include "eqbrtrd.mm"
include "climuni.mm"
include "syl2anc.mm"

theorem vonicclem2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  let vn: setvar n
  let cI: class I
  let cX: class X
  let vm: setvar m
  let vx: setvar x
  assume vonicclem2.x: |- ( ph -> X e. Fin )
  assume vonicclem2.a: |- ( ph -> A : X --> RR )
  assume vonicclem2.b: |- ( ph -> B : X --> RR )
  assume vonicclem2.n: |- ( ph -> X =/= (/) )
  assume vonicclem2.t: |- ( ( ph /\ k e. X ) -> ( A ` k ) <_ ( B ` k ) )
  assume vonicclem2.i: |- I = X_ k e. X ( ( A ` k ) [,] ( B ` k ) )
  assume vonicclem2.c: |- C = ( n e. NN |-> ( k e. X |-> ( ( B ` k ) + ( 1 / n ) ) ) )
  assume vonicclem2.d: |- D = ( n e. NN |-> X_ k e. X ( ( A ` k ) [,) ( ( C ` n ) ` k ) ) )

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
  disjoint A m
  disjoint k m
  disjoint m n
  disjoint B m
  disjoint C m
  disjoint D m
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
    vk
    cprod
    #
    cli
    wbr
    @5
    @9
    wceq
    wph
    @4
    vn
    cn
    @1
    ciin
    #
    @2
    cfv
    #
    @5
    cli
    wph
    @4
    vn
    cD
    c1
    @2
    c1
    cn
    wph
    vn
    nfv
    wph
    cX
    vonicclem2.x
    vonmea
    wph
    1zzd
    nnuz
    wph
    vn
    cn
    vk
    cX
    @8
    @6
    @0
    cC
    cfv
    #
    cfv
    #
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
    cA
    @12
    @16
    vk
    cX
    wph
    cX
    cfn
    wcel
    @17
    vonicclem2.x
    adantr
    #
    @16
    eqid
    wph
    cX
    cr
    cA
    wf
    @17
    vonicclem2.a
    adantr
    #
    @18
    cX
    cr
    @12
    wf
    cX
    cr
    vk
    cX
    @7
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
    @18
    vk
    cX
    @22
    cr
    @23
    @18
    @6
    cX
    wcel
    #
    wa
    #
    @7
    @21
    wph
    @24
    @7
    cr
    wcel
    @17
    wph
    cX
    cr
    @6
    cB
    vonicclem2.b
    ffvelrnda
    #
    adantlr
    #
    @17
    @21
    cr
    wcel
    wph
    @24
    @0
    nnrecre
    #
    ad2antlr
    #
    readdcld
    #
    @23
    eqid
    fmptd
    @18
    cX
    cr
    @12
    @23
    wph
    vn
    cn
    @23
    cC
    cvv
    cC
    vn
    cn
    @23
    cmpt
    #
    wceq
    wph
    vonicclem2.c
    a1i
    wph
    @23
    cvv
    wcel
    @17
    wph
    vk
    cX
    @22
    cfn
    vonicclem2.x
    mptexd
    adantr
    fvmpt2d
    #
    feq1d
    mpbird
    hoimbl
    #
    vonicclem2.d
    fmptd
    @18
    @0
    c1
    caddc
    co
    #
    cD
    cfv
    #
    @1
    wss
    vk
    cX
    @8
    @6
    @34
    cC
    cfv
    #
    cfv
    #
    cico
    co
    #
    cixp
    #
    @15
    wss
    @18
    vk
    cX
    @38
    @14
    @18
    vk
    nfv
    @25
    @8
    cxr
    wcel
    #
    @13
    cxr
    wcel
    @8
    @8
    cle
    wbr
    @37
    @13
    cle
    wbr
    #
    @38
    @14
    wss
    wph
    @24
    @40
    @17
    wph
    @24
    wa
    #
    cr
    cxr
    @8
    ressxr
    wph
    cX
    cr
    @6
    cA
    vonicclem2.a
    ffvelrnda
    #
    sseldi
    adantlr
    @25
    @13
    @25
    @13
    @22
    cr
    @18
    vk
    cX
    @22
    @12
    cvv
    @32
    @25
    @7
    @21
    caddc
    ovexd
    fvmpt2d
    #
    @30
    eqeltrd
    #
    rexrd
    @25
    @8
    @18
    cX
    cr
    @6
    cA
    @20
    ffvelrnda
    leidd
    @25
    @41
    @7
    c1
    @34
    cdiv
    co
    #
    caddc
    co
    #
    @22
    cle
    wbr
    @25
    @46
    @21
    @7
    @17
    @46
    cr
    wcel
    wph
    @24
    @17
    c1
    @34
    @17
    1red
    #
    @17
    @0
    c1
    @0
    nnre
    #
    @48
    readdcld
    @17
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
    @29
    @27
    @17
    @46
    @21
    cle
    wbr
    wph
    @24
    @17
    @46
    @21
    @51
    @28
    @17
    @0
    @34
    clt
    wbr
    @46
    @21
    clt
    wbr
    @17
    @0
    @49
    ltp1d
    @17
    @0
    @34
    @0
    nnrp
    @17
    @34
    @50
    nnrpd
    ltrecd
    mpbid
    ltled
    ad2antlr
    leadd2dd
    @25
    @37
    @47
    @13
    @22
    cle
    @18
    vk
    cX
    @47
    @36
    cvv
    @18
    vm
    @34
    vk
    cX
    @7
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
    @47
    cmpt
    #
    cn
    cC
    cvv
    cC
    vm
    cn
    @55
    cmpt
    #
    wceq
    @18
    cC
    @31
    @57
    vonicclem2.c
    vn
    vm
    cn
    @23
    @55
    @0
    @52
    wceq
    #
    vk
    cX
    @22
    @54
    @58
    @21
    @53
    @7
    caddc
    @0
    @52
    c1
    cdiv
    oveq2
    oveq2d
    mpteq2dv
    cbvmptv
    eqtri
    a1i
    @52
    @34
    wceq
    #
    @55
    @56
    wceq
    @18
    @59
    vk
    cX
    @54
    @47
    @59
    @53
    @46
    @7
    caddc
    @52
    @34
    c1
    cdiv
    oveq2
    oveq2d
    mpteq2dv
    adantl
    @18
    @0
    wph
    @17
    simpr
    peano2nnd
    #
    @18
    vk
    cX
    @47
    cfn
    @19
    mptexd
    fvmptd
    @25
    @7
    @46
    caddc
    ovexd
    fvmpt2d
    @44
    breq12d
    mpbird
    @8
    @13
    @8
    @37
    icossico
    syl22anc
    ixpssixp
    @18
    @35
    @39
    @1
    @15
    @18
    vm
    @34
    vk
    cX
    @8
    @6
    @52
    cC
    cfv
    #
    cfv
    #
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
    @64
    cmpt
    #
    wceq
    @18
    cD
    vn
    cn
    @15
    cmpt
    #
    @65
    vonicclem2.d
    vn
    vm
    cn
    @15
    @64
    @58
    vk
    cX
    @14
    @63
    @58
    @13
    @62
    @8
    cico
    @58
    @6
    @12
    @61
    @0
    @52
    cC
    fveq2
    fveq1d
    oveq2d
    ixpeq2dv
    cbvmptv
    eqtri
    a1i
    @59
    @64
    @39
    wceq
    @18
    @59
    vk
    cX
    @63
    @38
    @59
    @62
    @37
    @8
    cico
    @59
    @6
    @61
    @36
    @52
    @34
    cC
    fveq2
    fveq1d
    oveq2d
    ixpeq2dv
    adantl
    @60
    @39
    cvv
    wcel
    #
    @18
    @38
    cvv
    wcel
    #
    vk
    cX
    wral
    @67
    @68
    vk
    cX
    @8
    @37
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
    wph
    vn
    cn
    @15
    cD
    cvv
    cD
    @66
    wceq
    wph
    vonicclem2.d
    a1i
    #
    @18
    @15
    @16
    @33
    elexd
    fvmpt2d
    #
    sseq12d
    mpbird
    c1
    c1
    cuz
    cfv
    #
    wcel
    wph
    c1
    cn
    @71
    1nn
    nnuz
    eleqtri
    a1i
    wph
    c1
    cD
    cfv
    #
    @2
    cfv
    vk
    cX
    @8
    @6
    c1
    cC
    cfv
    #
    cfv
    #
    cico
    co
    #
    cixp
    #
    @2
    cfv
    cr
    wph
    @72
    @76
    @2
    wph
    vn
    c1
    @15
    @76
    cn
    cD
    cvv
    @69
    @0
    c1
    wceq
    #
    @15
    @76
    wceq
    wph
    @77
    vk
    cX
    @14
    @75
    @77
    @13
    @74
    @8
    cico
    @77
    @6
    @12
    @73
    @0
    c1
    cC
    fveq2
    fveq1d
    #
    oveq2d
    ixpeq2dv
    adantl
    c1
    cn
    wcel
    #
    wph
    1nn
    a1i
    @76
    cvv
    wcel
    #
    wph
    @75
    cvv
    wcel
    #
    vk
    cX
    wral
    @80
    @81
    vk
    cX
    @8
    @74
    cico
    ovex
    rgenw
    vk
    cX
    @75
    cvv
    ixpexg
    ax-mp
    a1i
    fvmptd
    fveq2d
    wph
    @8
    @74
    vk
    cX
    wph
    vk
    nfv
    #
    vonicclem2.x
    @43
    @42
    wph
    @79
    @24
    @74
    cr
    wcel
    #
    wph
    @24
    simpl
    @79
    @42
    1nn
    a1i
    wph
    @24
    simpr
    @25
    @13
    cr
    wcel
    #
    wi
    wph
    @79
    wa
    #
    @24
    wa
    #
    @83
    wi
    vn
    c1
    c1
    cn
    1nn
    elexi
    @77
    @25
    @86
    @84
    @83
    @77
    @18
    @85
    @24
    @77
    @17
    @79
    wph
    @0
    c1
    cn
    eleq1
    anbi2d
    anbi1d
    @77
    @13
    @74
    cr
    @78
    eleq1d
    imbi12d
    @45
    vtocl
    syl21anc
    vonhoire
    eqeltrd
    @4
    eqid
    meaiininc
    wph
    @5
    @11
    wph
    cI
    @10
    @2
    wph
    @10
    cI
    wph
    vn
    cn
    vk
    cX
    @8
    @22
    cico
    co
    #
    cixp
    #
    ciin
    vk
    cX
    @8
    @7
    cicc
    co
    cixp
    #
    @10
    cI
    wph
    @8
    @7
    vk
    vn
    cX
    @82
    @43
    @26
    iinhoiicc
    wph
    vn
    cn
    @1
    @88
    @18
    @1
    @15
    @88
    @70
    @18
    vk
    cX
    @14
    @87
    @25
    @13
    @22
    @8
    cico
    @44
    oveq2d
    ixpeq2dva
    eqtrd
    iineq2dv
    cI
    @89
    wceq
    wph
    vonicclem2.i
    a1i
    3eqtr4d
    eqcomd
    fveq2d
    eqcomd
    breqtrd
    wph
    @4
    vm
    cn
    @52
    cD
    cfv
    #
    @2
    cfv
    #
    cmpt
    #
    @9
    cli
    @4
    @92
    wceq
    wph
    vn
    vm
    cn
    @3
    @91
    @58
    @1
    @90
    @2
    @0
    @52
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
    @92
    vk
    vn
    cX
    vonicclem2.x
    vonicclem2.a
    vonicclem2.b
    vonicclem2.n
    vonicclem2.t
    vonicclem2.c
    vonicclem2.d
    @4
    @92
    @93
    eqcomi
    vonicclem1
    eqbrtrd
    @5
    @9
    @4
    climuni
    syl2anc
end
