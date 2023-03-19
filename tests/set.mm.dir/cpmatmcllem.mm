include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "cmulr.mm"
include "cfv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cco1.mm"
include "c0g.mm"
include "wceq.mm"
include "cn.mm"
include "wral.mm"
include "cbs.mm"
include "wi.mm"
include "eqid.mm"
include "cpmatelimp.mm"
include "adantr.mm"
include "ralcom.mm"
include "r19.26-2.mm"
include "bitr3i.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "simp-4r.mm"
include "simplrl.mm"
include "simpr.mm"
include "matecld.mm"
include "simplrr.mm"
include "jca32.mm"
include "adantlr.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "eqeq1d.mm"
include "oveq1.mm"
include "anbi12d.mm"
include "rspcva.mm"
include "a1i.mm"
include "exp4b.mm"
include "com23.mm"
include "imp31.mm"
include "ralimdva.mm"
include "impancom.mm"
include "imp.mm"
include "cply1mul.mm"
include "sylc.mm"
include "r19.21bi.mm"
include "an32s.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "cmnd.mm"
include "ringmnd.mm"
include "anim2i.mm"
include "ancomd.mm"
include "gsumz.mm"
include "syl.mm"
include "ad4antr.mm"
include "eqtrd.mm"
include "ex.mm"
include "ralrimi.mm"
include "wb.mm"
include "cn0.mm"
include "nnnn0.mm"
include "adantl.mm"
include "ply1ring.mm"
include "ad4antlr.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "ralrimiva.mm"
include "simp-4l.mm"
include "coe1fzgsumd.mm"
include "ralbidva.mm"
include "mpbird.mm"
include "syl5bi.mm"
include "expd.mm"
include "expr.mm"
include "impd.mm"
include "syld.mm"
include "imp32.mm"

theorem cpmatmcllem
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cP: class P
  let cR: class R
  let cS: class S
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cN: class N
  let vc: setvar c
  let vn: setvar n
  let va: setvar a
  let vb: setvar b
  let vl: setvar l
  assume cpmatsrngpmat.s: |- S = ( N ConstPolyMat R )
  assume cpmatsrngpmat.p: |- P = ( Poly1 ` R )
  assume cpmatsrngpmat.c: |- C = ( N Mat P )

  disjoint C i
  disjoint C j
  disjoint i j
  disjoint N i
  disjoint N j
  disjoint R i
  disjoint R j
  disjoint C c
  disjoint N c
  disjoint N x
  disjoint N y
  disjoint c i
  disjoint c j
  disjoint c x
  disjoint c y
  disjoint i x
  disjoint i y
  disjoint j x
  disjoint j y
  disjoint x y
  disjoint P c
  disjoint R c
  disjoint R x
  disjoint R y
  disjoint S y
  disjoint C k
  disjoint N k
  disjoint c k
  disjoint i k
  disjoint j k
  disjoint k x
  disjoint k y
  disjoint P k
  disjoint R k
  disjoint C n
  disjoint i n
  disjoint j n
  disjoint N n
  disjoint R n
  disjoint C a
  disjoint C b
  disjoint a b
  disjoint a c
  disjoint b c
  disjoint N a
  disjoint N b
  disjoint a i
  disjoint a j
  disjoint a x
  disjoint a y
  disjoint b i
  disjoint b j
  disjoint b x
  disjoint b y
  disjoint P a
  disjoint P b
  disjoint R a
  disjoint R b
  disjoint N l
  disjoint c l
  disjoint i l
  disjoint j l
  disjoint k l
  disjoint l x
  disjoint l y
  disjoint R l
  assert |- ( ( ( N e. Fin /\ R e. Ring ) /\ ( x e. S /\ y e. S ) ) -> A. i e. N A. j e. N A. c e. NN ( ( coe1 ` ( P gsum ( k e. N |-> ( ( i x k ) ( .r ` P ) ( k y j ) ) ) ) ) ` c ) = ( 0g ` R ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    wa
    #
    vx
    cv
    #
    cS
    wcel
    #
    vy
    cv
    #
    cS
    wcel
    #
    vc
    cv
    #
    cP
    vk
    cN
    vi
    cv
    #
    vk
    cv
    #
    @3
    co
    #
    @9
    vj
    cv
    #
    @5
    co
    #
    cP
    cmulr
    cfv
    #
    co
    #
    cmpt
    cgsu
    co
    cco1
    cfv
    cfv
    #
    cR
    c0g
    cfv
    #
    wceq
    #
    vc
    cn
    wral
    #
    vj
    cN
    wral
    #
    vi
    cN
    wral
    #
    @2
    @4
    @3
    cC
    cbs
    cfv
    #
    wcel
    #
    @7
    @8
    vl
    cv
    #
    @3
    co
    #
    cco1
    cfv
    #
    cfv
    #
    @16
    wceq
    #
    vc
    cn
    wral
    vl
    cN
    wral
    #
    vi
    cN
    wral
    #
    wa
    @6
    @20
    wi
    #
    @21
    cC
    cP
    cR
    cS
    vi
    vl
    vc
    @3
    cN
    cpmatsrngpmat.s
    cpmatsrngpmat.p
    cpmatsrngpmat.c
    @21
    eqid
    #
    cpmatelimp
    @2
    @22
    @29
    @30
    @2
    @22
    @29
    @30
    wi
    @2
    @22
    wa
    #
    @6
    @29
    @20
    @32
    @6
    @5
    @21
    wcel
    #
    @7
    @23
    @11
    @5
    co
    #
    cco1
    cfv
    #
    cfv
    #
    @16
    wceq
    #
    vc
    cn
    wral
    #
    vj
    cN
    wral
    vl
    cN
    wral
    #
    wa
    #
    @29
    @20
    wi
    #
    @2
    @6
    @40
    wi
    @22
    @21
    cC
    cP
    cR
    cS
    vl
    vj
    vc
    @5
    cN
    cpmatsrngpmat.s
    cpmatsrngpmat.p
    cpmatsrngpmat.c
    @31
    cpmatelimp
    adantr
    @32
    @33
    @39
    @41
    @2
    @22
    @33
    @39
    @41
    wi
    @2
    @22
    @33
    wa
    #
    wa
    #
    @39
    @41
    @43
    @39
    wa
    #
    @28
    @19
    vi
    cN
    @44
    @8
    cN
    wcel
    #
    @28
    @19
    wi
    #
    @43
    @45
    @39
    @46
    @43
    @45
    wa
    #
    @28
    @39
    @19
    @47
    @28
    @39
    @19
    wi
    @39
    @38
    vl
    cN
    wral
    #
    vj
    cN
    wral
    @47
    @28
    wa
    #
    @19
    @38
    vl
    vj
    cN
    cN
    ralcom
    @49
    @48
    @18
    vj
    cN
    @47
    @28
    @11
    cN
    wcel
    #
    @48
    @18
    wi
    #
    @47
    @50
    @28
    @51
    @43
    @45
    @50
    @28
    @51
    wi
    @43
    @45
    @50
    wa
    #
    wa
    #
    @28
    @48
    @18
    @28
    @48
    wa
    #
    @27
    @37
    wa
    #
    vl
    cN
    wral
    #
    vc
    cn
    wral
    #
    @53
    @18
    @54
    @55
    vc
    cn
    wral
    vl
    cN
    wral
    @57
    @27
    @37
    vl
    vc
    cN
    cn
    r19.26-2
    @55
    vl
    vc
    cN
    cn
    ralcom
    bitr3i
    @53
    @57
    @18
    @53
    @57
    wa
    #
    @18
    cR
    vk
    cN
    @7
    @14
    cco1
    cfv
    cfv
    #
    cmpt
    #
    cgsu
    co
    #
    @16
    wceq
    #
    vc
    cn
    wral
    #
    @58
    @62
    vc
    cn
    @53
    @57
    vc
    @53
    vc
    nfv
    @56
    vc
    cn
    nfra1
    nfan
    @58
    @7
    cn
    wcel
    #
    @62
    @58
    @64
    wa
    #
    @61
    cR
    vk
    cN
    @16
    cmpt
    #
    cgsu
    co
    #
    @16
    @65
    @60
    @66
    cR
    cgsu
    @65
    vk
    cN
    @59
    @16
    @58
    @9
    cN
    wcel
    #
    @64
    @59
    @16
    wceq
    #
    @58
    @68
    wa
    #
    @69
    vc
    cn
    @70
    @1
    @10
    cP
    cbs
    cfv
    #
    wcel
    #
    @12
    @71
    wcel
    #
    wa
    wa
    #
    @7
    @10
    cco1
    cfv
    #
    cfv
    #
    @16
    wceq
    #
    @7
    @12
    cco1
    cfv
    #
    cfv
    #
    @16
    wceq
    #
    wa
    #
    vc
    cn
    wral
    #
    @69
    vc
    cn
    wral
    @53
    @68
    @74
    @57
    @53
    @68
    wa
    #
    @1
    @72
    @73
    @0
    @1
    @42
    @52
    @68
    simp-4r
    @83
    cC
    @21
    cP
    @8
    @9
    @71
    @3
    cN
    cpmatsrngpmat.c
    @71
    eqid
    #
    @31
    @43
    @45
    @50
    @68
    simplrl
    @53
    @68
    simpr
    #
    @53
    @22
    @68
    @2
    @22
    @33
    @52
    simplrl
    adantr
    matecld
    #
    @83
    cC
    @21
    cP
    @9
    @11
    @71
    @5
    cN
    cpmatsrngpmat.c
    @84
    @31
    @85
    @43
    @45
    @50
    @68
    simplrr
    @53
    @33
    @68
    @2
    @22
    @33
    @52
    simplrr
    adantr
    matecld
    #
    jca32
    adantlr
    @58
    @68
    @82
    @53
    @68
    @57
    @82
    @83
    @56
    @81
    vc
    cn
    @53
    @68
    @64
    @56
    @81
    wi
    #
    @53
    @64
    @68
    @88
    @53
    @64
    @68
    @56
    @81
    @68
    @56
    wa
    @81
    wi
    @53
    @64
    wa
    #
    @55
    @81
    vl
    @9
    cN
    @23
    @9
    wceq
    #
    @27
    @77
    @37
    @80
    @90
    @26
    @76
    @16
    @90
    @7
    @25
    @75
    @90
    @24
    @10
    cco1
    @23
    @9
    @8
    @3
    oveq2
    fveq2d
    fveq1d
    eqeq1d
    @90
    @36
    @79
    @16
    @90
    @7
    @35
    @78
    @90
    @34
    @12
    cco1
    @23
    @9
    @11
    @5
    oveq1
    fveq2d
    fveq1d
    eqeq1d
    anbi12d
    rspcva
    a1i
    exp4b
    com23
    imp31
    ralimdva
    impancom
    imp
    @71
    cP
    cR
    @13
    @10
    @12
    @16
    vc
    cpmatsrngpmat.p
    @84
    @16
    eqid
    #
    @13
    eqid
    #
    cply1mul
    sylc
    r19.21bi
    an32s
    mpteq2dva
    oveq2d
    @2
    @67
    @16
    wceq
    #
    @42
    @52
    @57
    @64
    @2
    cR
    cmnd
    wcel
    #
    @0
    wa
    @93
    @2
    @0
    @94
    @1
    @94
    @0
    cR
    ringmnd
    anim2i
    ancomd
    cN
    vk
    cR
    cfn
    @16
    @91
    gsumz
    syl
    ad4antr
    eqtrd
    ex
    ralrimi
    @53
    @18
    @63
    wb
    @57
    @53
    @17
    @62
    vc
    cn
    @89
    @15
    @61
    @16
    @89
    vk
    @71
    cP
    cR
    @7
    @14
    cN
    cpmatsrngpmat.p
    @84
    @0
    @1
    @42
    @52
    @64
    simp-4r
    @64
    @7
    cn0
    wcel
    @53
    @7
    nnnn0
    adantl
    @53
    @14
    @71
    wcel
    #
    vk
    cN
    wral
    @64
    @53
    @95
    vk
    cN
    @83
    cP
    crg
    wcel
    #
    @72
    @73
    @95
    @1
    @96
    @0
    @42
    @52
    @68
    cP
    cR
    cpmatsrngpmat.p
    ply1ring
    ad4antlr
    @86
    @87
    @71
    cP
    @13
    @10
    @12
    @84
    @92
    ringcl
    syl3anc
    ralrimiva
    adantr
    @0
    @1
    @42
    @52
    @64
    simp-4l
    coe1fzgsumd
    eqeq1d
    ralbidva
    adantr
    mpbird
    ex
    syl5bi
    expd
    expr
    com23
    imp31
    ralimdva
    syl5bi
    ex
    com23
    impancom
    imp
    ralimdva
    ex
    expr
    impd
    syld
    com23
    ex
    impd
    syld
    imp32
end
