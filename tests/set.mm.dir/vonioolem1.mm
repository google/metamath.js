include "cv.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cprod.mm"
include "cli.mm"
include "wbr.mm"
include "cn.mm"
include "c1.mm"
include "cdiv.mm"
include "cmpt.mm"
include "wceq.mm"
include "a1i.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "cvv.mm"
include "cfn.mm"
include "mptexd.mm"
include "adantr.mm"
include "fvmpt2d.mm"
include "ovexd.mm"
include "oveq2d.mm"
include "cr.mm"
include "ffvelrnda.mm"
include "adantlr.mm"
include "recnd.mm"
include "wf.mm"
include "nnrecre.mm"
include "ad2antlr.mm"
include "subsub4d.mm"
include "eqtr4d.mm"
include "prodeq2dv.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "nfv.mm"
include "crp.mm"
include "rpssre.mm"
include "clt.mm"
include "wb.mm"
include "difrp.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "sseldi.mm"
include "eqid.mm"
include "fprodsubrecnncnv.mm"
include "eqbrtrd.mm"
include "nnex.mm"
include "mptex.mm"
include "syl5eqel.mm"
include "cvoln.mm"
include "cfl.mm"
include "cz.mm"
include "cn0.mm"
include "cc0.mm"
include "cle.mm"
include "1rp.mm"
include "crn.mm"
include "rnmptssd.mm"
include "cinf.mm"
include "wor.mm"
include "c0.mm"
include "wne.mm"
include "wss.mm"
include "ltso.mm"
include "rnmptfi.mm"
include "syl.mm"
include "rnmptn0.mm"
include "sstrd.mm"
include "fiinfcl.mm"
include "syl13anc.mm"
include "sseldd.mm"
include "rpdivcld.mm"
include "rpred.mm"
include "rpge0d.mm"
include "flge0nn0.mm"
include "nn0p1nn.mm"
include "nnzd.mm"
include "cico.mm"
include "cixp.mm"
include "cvol.mm"
include "cuz.mm"
include "recnnltrp.mm"
include "simpld.mm"
include "uznnssnn.mm"
include "syl5eqss.mm"
include "simpr.mm"
include "cdm.mm"
include "readdcld.mm"
include "fmptd.mm"
include "feq1d.mm"
include "mpbird.mm"
include "hoimbl.mm"
include "elexd.mm"
include "syldan.mm"
include "fveq2d.mm"
include "vonn0hoi.mm"
include "cif.mm"
include "syldanl.mm"
include "volico.mm"
include "nnrecred.mm"
include "ad2antrr.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "eluzle.mm"
include "adantl.mm"
include "nnrpd.mm"
include "nnrp.mm"
include "lerecd.mm"
include "simprd.mm"
include "id.mm"
include "elrnmpt1.mm"
include "infrefilb.mm"
include "syl3anc.mm"
include "syl5eqbr.mm"
include "ltletrd.mm"
include "lelttrd.mm"
include "ltaddsub2d.mm"
include "iftrued.mm"
include "3eqtrd.mm"
include "fvexd.mm"
include "fvmpt2.mm"
include "prodex.mm"
include "3eqtr4rd.mm"
include "climeq.mm"

theorem vonioolem1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cT: class T
  let vk: setvar k
  let vn: setvar n
  let cE: class E
  let cN: class N
  let cX: class X
  let cZ: class Z
  let vx: setvar x
  assume vonioolem1.x: |- ( ph -> X e. Fin )
  assume vonioolem1.a: |- ( ph -> A : X --> RR )
  assume vonioolem1.b: |- ( ph -> B : X --> RR )
  assume vonioolem1.u: |- ( ph -> X =/= (/) )
  assume vonioolem1.t: |- ( ( ph /\ k e. X ) -> ( A ` k ) < ( B ` k ) )
  assume vonioolem1.c: |- C = ( n e. NN |-> ( k e. X |-> ( ( A ` k ) + ( 1 / n ) ) ) )
  assume vonioolem1.d: |- D = ( n e. NN |-> X_ k e. X ( ( ( C ` n ) ` k ) [,) ( B ` k ) ) )
  assume vonioolem1.s: |- S = ( n e. NN |-> ( ( voln ` X ) ` ( D ` n ) ) )
  assume vonioolem1.r: |- T = ( n e. NN |-> prod_ k e. X ( ( B ` k ) - ( ( C ` n ) ` k ) ) )
  assume vonioolem1.e: |- E = inf ( ran ( k e. X |-> ( ( B ` k ) - ( A ` k ) ) ) , RR , < )
  assume vonioolem1.n: |- N = ( ( |_ ` ( 1 / E ) ) + 1 )
  assume vonioolem1.z: |- Z = ( ZZ>= ` N )

  disjoint A n
  disjoint B k
  disjoint B n
  disjoint k n
  disjoint C k
  disjoint S n
  disjoint T n
  disjoint X k
  disjoint X n
  disjoint Z k
  disjoint Z n
  disjoint k ph
  disjoint n ph
  disjoint k x
  assert |- ( ph -> S ~~> prod_ k e. X ( ( B ` k ) - ( A ` k ) ) )

  proof
    wph
    cT
    cX
    vk
    cv
    #
    cB
    cfv
    #
    @0
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
    cS
    @4
    cli
    wbr
    wph
    cT
    vn
    cn
    cX
    @3
    c1
    vn
    cv
    #
    cdiv
    co
    #
    cmin
    co
    #
    vk
    cprod
    #
    cmpt
    #
    @4
    cli
    wph
    cT
    vn
    cn
    cX
    @1
    @0
    @5
    cC
    cfv
    #
    cfv
    #
    cmin
    co
    #
    vk
    cprod
    #
    cmpt
    #
    @9
    cT
    @14
    wceq
    wph
    vonioolem1.r
    a1i
    wph
    vn
    cn
    @13
    @8
    wph
    @5
    cn
    wcel
    #
    wa
    #
    cX
    @12
    @7
    vk
    @16
    @0
    cX
    wcel
    #
    wa
    #
    @12
    @1
    @2
    @6
    caddc
    co
    #
    cmin
    co
    @7
    @18
    @11
    @19
    @1
    cmin
    @16
    vk
    cX
    @19
    @10
    cvv
    wph
    vn
    cn
    vk
    cX
    @19
    cmpt
    #
    cC
    cvv
    cC
    vn
    cn
    @20
    cmpt
    wceq
    wph
    vonioolem1.c
    a1i
    wph
    @20
    cvv
    wcel
    @15
    wph
    vk
    cX
    @19
    cfn
    vonioolem1.x
    mptexd
    adantr
    fvmpt2d
    #
    @18
    @2
    @6
    caddc
    ovexd
    fvmpt2d
    #
    oveq2d
    @18
    @1
    @2
    @6
    @18
    @1
    wph
    @17
    @1
    cr
    wcel
    #
    @15
    wph
    cX
    cr
    @0
    cB
    vonioolem1.b
    ffvelrnda
    #
    adantlr
    #
    recnd
    @18
    @2
    @16
    cX
    cr
    @0
    cA
    wph
    cX
    cr
    cA
    wf
    @15
    vonioolem1.a
    adantr
    ffvelrnda
    #
    recnd
    @18
    @6
    @15
    @6
    cr
    wcel
    #
    wph
    @17
    @5
    nnrecre
    ad2antlr
    #
    recnd
    subsub4d
    eqtr4d
    prodeq2dv
    mpteq2dva
    eqtrd
    wph
    @3
    @9
    vk
    vn
    cX
    wph
    vk
    nfv
    #
    vonioolem1.x
    wph
    @17
    wa
    #
    @3
    @30
    crp
    cr
    @3
    rpssre
    @30
    @2
    @1
    clt
    wbr
    #
    @3
    crp
    wcel
    #
    vonioolem1.t
    @30
    @2
    cr
    wcel
    #
    @23
    @31
    @32
    wb
    wph
    cX
    cr
    @0
    cA
    vonioolem1.a
    ffvelrnda
    @24
    @2
    @1
    difrp
    syl2anc
    mpbid
    #
    sseldi
    #
    recnd
    @9
    eqid
    fprodsubrecnncnv
    eqbrtrd
    wph
    @4
    vn
    cT
    cS
    cN
    cvv
    cvv
    cZ
    vonioolem1.z
    wph
    cT
    @14
    cvv
    vonioolem1.r
    @14
    cvv
    wcel
    wph
    vn
    cn
    @13
    nnex
    mptex
    a1i
    syl5eqel
    wph
    cS
    vn
    cn
    @5
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
    cvv
    vonioolem1.s
    @39
    cvv
    wcel
    wph
    vn
    cn
    @38
    nnex
    mptex
    a1i
    syl5eqel
    wph
    cN
    c1
    cE
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
    cz
    vonioolem1.n
    wph
    @42
    wph
    @41
    cn0
    wcel
    #
    @42
    cn
    wcel
    wph
    @40
    cr
    wcel
    cc0
    @40
    cle
    wbr
    @43
    wph
    @40
    wph
    c1
    cE
    c1
    crp
    wcel
    wph
    1rp
    a1i
    wph
    vk
    cX
    @3
    cmpt
    #
    crn
    #
    crp
    cE
    wph
    vk
    cX
    @3
    crp
    @44
    @29
    @44
    eqid
    #
    @34
    rnmptssd
    #
    wph
    cE
    @45
    cr
    clt
    cinf
    #
    @45
    vonioolem1.e
    wph
    cr
    clt
    wor
    #
    @45
    cfn
    wcel
    #
    @45
    c0
    wne
    @45
    cr
    wss
    #
    @48
    @45
    wcel
    @49
    wph
    ltso
    a1i
    wph
    cX
    cfn
    wcel
    #
    @50
    vonioolem1.x
    vk
    @44
    cX
    @3
    @46
    rnmptfi
    syl
    #
    wph
    vk
    cX
    @3
    @44
    crp
    @29
    @34
    @46
    vonioolem1.u
    rnmptn0
    wph
    @45
    crp
    cr
    @47
    crp
    cr
    wss
    wph
    rpssre
    a1i
    sstrd
    #
    cr
    @45
    clt
    fiinfcl
    syl13anc
    syl5eqel
    sseldd
    #
    rpdivcld
    #
    rpred
    wph
    @40
    @56
    rpge0d
    @40
    flge0nn0
    syl2anc
    @41
    nn0p1nn
    syl
    nnzd
    syl5eqel
    wph
    @5
    cZ
    wcel
    #
    wa
    #
    @38
    @13
    @5
    cS
    cfv
    #
    @5
    cT
    cfv
    #
    @58
    @38
    vk
    cX
    @11
    @1
    cico
    co
    #
    cixp
    #
    @37
    cfv
    cX
    @61
    cvol
    cfv
    #
    vk
    cprod
    @13
    @58
    @36
    @62
    @37
    wph
    @57
    @15
    @36
    @62
    wceq
    @58
    cZ
    cn
    @5
    wph
    cZ
    cn
    wss
    @57
    wph
    cZ
    cN
    cuz
    cfv
    #
    cn
    vonioolem1.z
    wph
    cN
    cn
    wcel
    #
    @64
    cn
    wss
    wph
    @65
    c1
    cN
    cdiv
    co
    #
    cE
    clt
    wbr
    #
    wph
    cE
    crp
    wcel
    @65
    @67
    wa
    @55
    cE
    cN
    vonioolem1.n
    recnnltrp
    syl
    #
    simpld
    #
    cN
    uznnssnn
    syl
    syl5eqss
    adantr
    wph
    @57
    simpr
    sseldd
    #
    wph
    vn
    cn
    @62
    cD
    cvv
    cD
    vn
    cn
    @62
    cmpt
    wceq
    wph
    vonioolem1.d
    a1i
    @16
    @62
    @37
    cdm
    #
    @16
    @10
    cB
    @71
    vk
    cX
    wph
    @52
    @15
    vonioolem1.x
    adantr
    @71
    eqid
    @16
    cX
    cr
    @10
    wf
    #
    cX
    cr
    @20
    wf
    @16
    vk
    cX
    @19
    cr
    @20
    @18
    @2
    @6
    @26
    @28
    readdcld
    @20
    eqid
    fmptd
    @16
    cX
    cr
    @10
    @20
    @21
    feq1d
    mpbird
    #
    wph
    cX
    cr
    cB
    wf
    #
    @15
    vonioolem1.b
    adantr
    hoimbl
    elexd
    fvmpt2d
    syldan
    fveq2d
    @58
    @10
    cB
    vk
    @62
    cX
    wph
    @52
    @57
    vonioolem1.x
    adantr
    wph
    cX
    c0
    wne
    @57
    vonioolem1.u
    adantr
    wph
    @57
    @15
    @72
    @70
    @73
    syldan
    #
    wph
    @74
    @57
    vonioolem1.b
    adantr
    @62
    eqid
    vonn0hoi
    @58
    cX
    @63
    @12
    vk
    @58
    @17
    wa
    #
    @63
    @11
    @1
    clt
    wbr
    #
    @12
    cc0
    cif
    #
    @12
    @76
    @11
    cr
    wcel
    @23
    @63
    @78
    wceq
    @58
    cX
    cr
    @0
    @10
    @75
    ffvelrnda
    wph
    @57
    @15
    @17
    @23
    @70
    @25
    syldanl
    #
    @11
    @1
    volico
    syl2anc
    @76
    @77
    @12
    cc0
    @76
    @11
    @19
    @1
    clt
    wph
    @57
    @15
    @17
    @11
    @19
    wceq
    @70
    @22
    syldanl
    @76
    @19
    @1
    clt
    wbr
    @6
    @3
    clt
    wbr
    @76
    @6
    @66
    @3
    wph
    @57
    @15
    @17
    @27
    @70
    @28
    syldanl
    #
    wph
    @66
    cr
    wcel
    #
    @57
    @17
    wph
    cN
    @69
    nnrecred
    #
    ad2antrr
    wph
    @17
    @3
    cr
    wcel
    @57
    @35
    adantlr
    @58
    @6
    @66
    cle
    wbr
    #
    @17
    @58
    cN
    @5
    cle
    wbr
    #
    @83
    @57
    @84
    wph
    @57
    @5
    @64
    wcel
    #
    @84
    @57
    @85
    cZ
    @64
    @5
    vonioolem1.z
    eleq2i
    biimpi
    cN
    @5
    eluzle
    syl
    adantl
    @58
    cN
    @5
    wph
    cN
    crp
    wcel
    @57
    wph
    cN
    @69
    nnrpd
    adantr
    @58
    @15
    @5
    crp
    wcel
    @70
    @5
    nnrp
    syl
    lerecd
    mpbid
    adantr
    wph
    @17
    @66
    @3
    clt
    wbr
    @57
    @30
    @66
    cE
    @3
    wph
    @81
    @17
    @82
    adantr
    wph
    cE
    cr
    wcel
    @17
    wph
    crp
    cr
    cE
    rpssre
    @55
    sseldi
    adantr
    @35
    wph
    @67
    @17
    wph
    @65
    @67
    @68
    simprd
    adantr
    @30
    cE
    @48
    @3
    cle
    vonioolem1.e
    @30
    @51
    @50
    @3
    @45
    wcel
    #
    @48
    @3
    cle
    wbr
    wph
    @51
    @17
    @54
    adantr
    wph
    @50
    @17
    @53
    adantr
    @17
    @86
    wph
    @17
    @17
    @3
    cvv
    wcel
    @86
    @17
    id
    @17
    @1
    @2
    cmin
    ovexd
    vk
    cX
    @3
    @44
    cvv
    @46
    elrnmpt1
    syl2anc
    adantl
    @3
    @45
    infrefilb
    syl3anc
    syl5eqbr
    ltletrd
    adantlr
    lelttrd
    @76
    @2
    @6
    @1
    wph
    @57
    @15
    @17
    @33
    @70
    @26
    syldanl
    @80
    @79
    ltaddsub2d
    mpbird
    eqbrtrd
    iftrued
    eqtrd
    prodeq2dv
    3eqtrd
    @58
    @15
    @38
    cvv
    wcel
    @59
    @38
    wceq
    @70
    @58
    @36
    @37
    fvexd
    vn
    cn
    @38
    cvv
    cS
    vonioolem1.s
    fvmpt2
    syl2anc
    @58
    @15
    @13
    cvv
    wcel
    #
    @60
    @13
    wceq
    @70
    @87
    @58
    cX
    @12
    vk
    prodex
    a1i
    vn
    cn
    @13
    cvv
    cT
    vonioolem1.r
    fvmpt2
    syl2anc
    3eqtr4rd
    climeq
    mpbid
end
