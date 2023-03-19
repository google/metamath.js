include "cn.mm"
include "wcel.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "wi.mm"
include "wral.mm"
include "cdvds.mm"
include "wbr.mm"
include "cprime.mm"
include "c1.mm"
include "wceq.mm"
include "breq2.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "nncn.mm"
include "mulid1d.mm"
include "biimpd.mm"
include "rgen.mm"
include "a1i.mm"
include "breq1.mm"
include "eleq1.mm"
include "rspcv.mm"
include "cz.mm"
include "prmz.mm"
include "iddvds.mm"
include "syl.mm"
include "wa.mm"
include "simprl.mm"
include "simpll.mm"
include "simprr.mm"
include "simplr.mm"
include "2sqlem5.mm"
include "expr.mm"
include "ralrimiva.mm"
include "ex.mm"
include "embantd.mm"
include "syld.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "prth.mm"
include "wo.mm"
include "wb.mm"
include "simpr.mm"
include "eluzelz.mm"
include "ad2antrr.mm"
include "ad2antlr.mm"
include "euclemma.mm"
include "syl3anc.mm"
include "jaob.mm"
include "syl6bb.mm"
include "ralbidva.mm"
include "r19.26.mm"
include "biimpa.mm"
include "oveq1.mm"
include "cbvralv.mm"
include "cc.mm"
include "adantl.mm"
include "uzssz.mm"
include "zsscn.mm"
include "sstri.mm"
include "sseldi.mm"
include "w3a.mm"
include "mul32.mm"
include "mulass.mm"
include "eqtr3d.mm"
include "eluz2nn.mm"
include "nnmulcld.mm"
include "sylc.mm"
include "sylbird.mm"
include "imim1d.mm"
include "ralimdva.mm"
include "sylan2b.mm"
include "expimpd.mm"
include "com23.mm"
include "syl5.mm"
include "prmind.mm"
include "syl3c.mm"

theorem 2sqlem6
  let wph: wff ph
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cS: class S
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vn: setvar n
  let vq: setvar q
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vm: setvar m
  let cC: class C
  let vu: setvar u
  let vv: setvar v
  let cM: class M
  let cD: class D
  let cE: class E
  let cN: class N
  let cY: class Y
  let cF: class F
  let cP: class P
  assume 2sq.1: |- S = ran ( w e. Z[i] |-> ( ( abs ` w ) ^ 2 ) )
  assume 2sqlem6.1: |- ( ph -> A e. NN )
  assume 2sqlem6.2: |- ( ph -> B e. NN )
  assume 2sqlem6.3: |- ( ph -> A. p e. Prime ( p || B -> p e. S ) )
  assume 2sqlem6.4: |- ( ph -> ( A x. B ) e. S )

  disjoint p w
  disjoint p ph
  disjoint B p
  disjoint S p
  disjoint a b
  disjoint a n
  disjoint a p
  disjoint a q
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b n
  disjoint b p
  disjoint b q
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint n p
  disjoint n q
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint p q
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint q w
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint a m
  disjoint A a
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint C x
  disjoint p u
  disjoint p v
  disjoint q u
  disjoint q v
  disjoint ph q
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint ph u
  disjoint v x
  disjoint v y
  disjoint ph v
  disjoint ph x
  disjoint ph y
  disjoint B a
  disjoint b m
  disjoint B b
  disjoint m p
  disjoint B m
  disjoint B x
  disjoint B y
  disjoint a u
  disjoint a v
  disjoint M a
  disjoint b u
  disjoint b v
  disjoint M b
  disjoint M p
  disjoint u z
  disjoint M u
  disjoint v z
  disjoint M v
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint S a
  disjoint S b
  disjoint m n
  disjoint m q
  disjoint m u
  disjoint m v
  disjoint S m
  disjoint n u
  disjoint n v
  disjoint S n
  disjoint S q
  disjoint S u
  disjoint S v
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint D x
  disjoint E a
  disjoint E p
  disjoint E x
  disjoint E y
  disjoint E z
  disjoint N p
  disjoint N q
  disjoint N u
  disjoint N v
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint Y a
  disjoint Y b
  disjoint Y m
  disjoint Y n
  disjoint Y x
  disjoint Y y
  disjoint F a
  disjoint F p
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint P n
  disjoint P p
  disjoint P q
  disjoint P x
  disjoint P y
  assert |- ( ph -> A e. S )

  proof
    wph
    cA
    cn
    wcel
    vm
    cv
    #
    cB
    cmul
    co
    #
    cS
    wcel
    #
    @0
    cS
    wcel
    #
    wi
    #
    vm
    cn
    wral
    #
    cA
    cB
    cmul
    co
    #
    cS
    wcel
    #
    cA
    cS
    wcel
    #
    2sqlem6.1
    wph
    cB
    cn
    wcel
    vp
    cv
    #
    cB
    cdvds
    wbr
    #
    @9
    cS
    wcel
    #
    wi
    #
    vp
    cprime
    wral
    #
    @5
    2sqlem6.2
    2sqlem6.3
    @9
    vx
    cv
    #
    cdvds
    wbr
    #
    @11
    wi
    #
    vp
    cprime
    wral
    #
    @0
    @14
    cmul
    co
    #
    cS
    wcel
    #
    @3
    wi
    #
    vm
    cn
    wral
    #
    wi
    @9
    c1
    cdvds
    wbr
    #
    @11
    wi
    #
    vp
    cprime
    wral
    #
    @0
    c1
    cmul
    co
    #
    cS
    wcel
    #
    @3
    wi
    #
    vm
    cn
    wral
    #
    wi
    @9
    vy
    cv
    #
    cdvds
    wbr
    #
    @11
    wi
    #
    vp
    cprime
    wral
    #
    @0
    @29
    cmul
    co
    #
    cS
    wcel
    #
    @3
    wi
    #
    vm
    cn
    wral
    #
    wi
    #
    @9
    vz
    cv
    #
    cdvds
    wbr
    #
    @11
    wi
    #
    vp
    cprime
    wral
    #
    @0
    @38
    cmul
    co
    #
    cS
    wcel
    #
    @3
    wi
    #
    vm
    cn
    wral
    #
    wi
    #
    @9
    @29
    @38
    cmul
    co
    #
    cdvds
    wbr
    #
    @11
    wi
    #
    vp
    cprime
    wral
    #
    @0
    @47
    cmul
    co
    #
    cS
    wcel
    #
    @3
    wi
    #
    vm
    cn
    wral
    #
    wi
    #
    @13
    @5
    wi
    vx
    vy
    vz
    cB
    @14
    c1
    wceq
    #
    @17
    @24
    @21
    @28
    @56
    @16
    @23
    vp
    cprime
    @56
    @15
    @22
    @11
    @14
    c1
    @9
    cdvds
    breq2
    imbi1d
    ralbidv
    @56
    @20
    @27
    vm
    cn
    @56
    @19
    @26
    @3
    @56
    @18
    @25
    cS
    @14
    c1
    @0
    cmul
    oveq2
    eleq1d
    imbi1d
    ralbidv
    imbi12d
    @14
    @29
    wceq
    #
    @17
    @32
    @21
    @36
    @57
    @16
    @31
    vp
    cprime
    @57
    @15
    @30
    @11
    @14
    @29
    @9
    cdvds
    breq2
    imbi1d
    ralbidv
    @57
    @20
    @35
    vm
    cn
    @57
    @19
    @34
    @3
    @57
    @18
    @33
    cS
    @14
    @29
    @0
    cmul
    oveq2
    eleq1d
    imbi1d
    ralbidv
    imbi12d
    @14
    @38
    wceq
    #
    @17
    @41
    @21
    @45
    @58
    @16
    @40
    vp
    cprime
    @58
    @15
    @39
    @11
    @14
    @38
    @9
    cdvds
    breq2
    imbi1d
    ralbidv
    @58
    @20
    @44
    vm
    cn
    @58
    @19
    @43
    @3
    @58
    @18
    @42
    cS
    @14
    @38
    @0
    cmul
    oveq2
    eleq1d
    imbi1d
    ralbidv
    imbi12d
    @14
    @47
    wceq
    #
    @17
    @50
    @21
    @54
    @59
    @16
    @49
    vp
    cprime
    @59
    @15
    @48
    @11
    @14
    @47
    @9
    cdvds
    breq2
    imbi1d
    ralbidv
    @59
    @20
    @53
    vm
    cn
    @59
    @19
    @52
    @3
    @59
    @18
    @51
    cS
    @14
    @47
    @0
    cmul
    oveq2
    eleq1d
    imbi1d
    ralbidv
    imbi12d
    @14
    cB
    wceq
    #
    @17
    @13
    @21
    @5
    @60
    @16
    @12
    vp
    cprime
    @60
    @15
    @10
    @11
    @14
    cB
    @9
    cdvds
    breq2
    imbi1d
    ralbidv
    @60
    @20
    @4
    vm
    cn
    @60
    @19
    @2
    @3
    @60
    @18
    @1
    cS
    @14
    cB
    @0
    cmul
    oveq2
    eleq1d
    imbi1d
    ralbidv
    imbi12d
    @28
    @24
    @27
    vm
    cn
    @0
    cn
    wcel
    #
    @26
    @3
    @61
    @25
    @0
    cS
    @61
    @0
    @0
    nncn
    #
    mulid1d
    eleq1d
    biimpd
    rgen
    a1i
    @14
    cprime
    wcel
    #
    @17
    @14
    @14
    cdvds
    wbr
    #
    @14
    cS
    wcel
    #
    wi
    #
    @21
    @16
    @66
    vp
    @14
    cprime
    @9
    @14
    wceq
    @15
    @64
    @11
    @65
    @9
    @14
    @14
    cdvds
    breq1
    @9
    @14
    cS
    eleq1
    imbi12d
    rspcv
    @63
    @64
    @65
    @21
    @63
    @14
    cz
    wcel
    @64
    @14
    prmz
    @14
    iddvds
    syl
    @63
    @65
    @21
    @63
    @65
    wa
    #
    @20
    vm
    cn
    @67
    @61
    @19
    @3
    @67
    @61
    @19
    wa
    #
    wa
    vw
    @14
    cS
    @0
    2sq.1
    @67
    @61
    @19
    simprl
    @63
    @65
    @68
    simpll
    @67
    @61
    @19
    simprr
    @63
    @65
    @68
    simplr
    2sqlem5
    expr
    ralrimiva
    ex
    embantd
    syld
    @37
    @46
    wa
    @32
    @41
    wa
    #
    @36
    @45
    wa
    #
    wi
    #
    @29
    c2
    cuz
    cfv
    #
    wcel
    #
    @38
    @72
    wcel
    #
    wa
    #
    @55
    @32
    @36
    @41
    @45
    prth
    @75
    @50
    @71
    @54
    @75
    @50
    @71
    @54
    wi
    @75
    @50
    wa
    #
    @69
    @70
    @54
    @75
    @50
    @69
    @75
    @50
    @31
    @40
    wa
    #
    vp
    cprime
    wral
    @69
    @75
    @49
    @77
    vp
    cprime
    @75
    @9
    cprime
    wcel
    #
    wa
    #
    @49
    @30
    @39
    wo
    #
    @11
    wi
    @77
    @79
    @48
    @80
    @11
    @79
    @78
    @29
    cz
    wcel
    #
    @38
    cz
    wcel
    #
    @48
    @80
    wb
    @75
    @78
    simpr
    @73
    @81
    @74
    @78
    c2
    @29
    eluzelz
    ad2antrr
    @74
    @82
    @73
    @78
    c2
    @38
    eluzelz
    ad2antlr
    @9
    @29
    @38
    euclemma
    syl3anc
    imbi1d
    @30
    @11
    @39
    jaob
    syl6bb
    ralbidva
    @31
    @40
    vp
    cprime
    r19.26
    syl6bb
    biimpa
    @76
    @36
    @45
    @54
    @36
    @76
    vn
    cv
    #
    @29
    cmul
    co
    #
    cS
    wcel
    #
    @83
    cS
    wcel
    #
    wi
    #
    vn
    cn
    wral
    #
    @45
    @54
    wi
    @35
    @87
    vm
    vn
    cn
    @0
    @83
    wceq
    #
    @34
    @85
    @3
    @86
    @89
    @33
    @84
    cS
    @0
    @83
    @29
    cmul
    oveq1
    eleq1d
    @0
    @83
    cS
    eleq1
    imbi12d
    cbvralv
    @76
    @88
    wa
    #
    @44
    @53
    vm
    cn
    @90
    @61
    wa
    #
    @52
    @43
    @3
    @91
    @52
    @42
    @29
    cmul
    co
    #
    cS
    wcel
    #
    @43
    @91
    @92
    @51
    cS
    @91
    @0
    cc
    wcel
    #
    @29
    cc
    wcel
    #
    @38
    cc
    wcel
    #
    @92
    @51
    wceq
    @61
    @94
    @90
    @62
    adantl
    @91
    @72
    cc
    @29
    @72
    cz
    cc
    c2
    uzssz
    zsscn
    sstri
    #
    @76
    @73
    @88
    @61
    @73
    @74
    @50
    simpll
    ad2antrr
    sseldi
    @91
    @72
    cc
    @38
    @97
    @76
    @74
    @88
    @61
    @73
    @74
    @50
    simplr
    ad2antrr
    #
    sseldi
    @94
    @95
    @96
    w3a
    @33
    @38
    cmul
    co
    @92
    @51
    @0
    @29
    @38
    mul32
    @0
    @29
    @38
    mulass
    eqtr3d
    syl3anc
    eleq1d
    @91
    @42
    cn
    wcel
    @88
    @93
    @43
    wi
    #
    @91
    @0
    @38
    @90
    @61
    simpr
    @91
    @74
    @38
    cn
    wcel
    @98
    @38
    eluz2nn
    syl
    nnmulcld
    @76
    @88
    @61
    simplr
    @87
    @99
    vn
    @42
    cn
    @83
    @42
    wceq
    #
    @85
    @93
    @86
    @43
    @100
    @84
    @92
    cS
    @83
    @42
    @29
    cmul
    oveq1
    eleq1d
    @83
    @42
    cS
    eleq1
    imbi12d
    rspcv
    sylc
    sylbird
    imim1d
    ralimdva
    sylan2b
    expimpd
    embantd
    ex
    com23
    syl5
    prmind
    sylc
    2sqlem6.4
    @4
    @7
    @8
    wi
    vm
    cA
    cn
    @0
    cA
    wceq
    #
    @2
    @7
    @3
    @8
    @101
    @1
    @6
    cS
    @0
    cA
    cB
    cmul
    oveq1
    eleq1d
    @0
    cA
    cS
    eleq1
    imbi12d
    rspcv
    syl3c
end
