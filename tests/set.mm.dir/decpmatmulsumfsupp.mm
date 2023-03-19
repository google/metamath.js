include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cv.mm"
include "cvv.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cdecpmat.mm"
include "cmin.mm"
include "cmpt.mm"
include "cgsu.mm"
include "c0g.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "cn0.mm"
include "ovexd.mm"
include "wceq.mm"
include "oveq2.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "mpteq12dv.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "cmulr.mm"
include "cco1.mm"
include "cmpt2.mm"
include "simpll.mm"
include "simplr.mm"
include "w3a.mm"
include "pmatring.mm"
include "anim1i.mm"
include "3anass.mm"
include "sylibr.mm"
include "eqid.mm"
include "ringcl.mm"
include "syl.mm"
include "pmatcoe1fsupp.mm"
include "syl3anc.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "eqeq1d.mm"
include "rspc2va.mm"
include "expcom.mm"
include "adantl.mm"
include "3impib.mm"
include "mpt2eq3dva.mm"
include "mat0op.mm"
include "syl5eq.mm"
include "ad3antrrr.mm"
include "eqtr4d.mm"
include "ex.mm"
include "imim2d.mm"
include "ralimdva.mm"
include "reximdv.mm"
include "mpd.mm"
include "oveqi.mm"
include "mpteq2dv.mm"
include "simpllr.mm"
include "simpr.mm"
include "decpmatmul.mm"
include "decpmatval.mm"
include "sylan.mm"
include "3eqtr2d.mm"
include "imbi2d.mm"
include "ralbidva.mm"
include "rexbidv.mm"
include "mpbird.mm"
include "mptnn0fsuppd.mm"

theorem decpmatmulsumfsupp
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let c.x: class .x.
  let vk: setvar k
  let cN: class N
  let c.0: class .0.
  let vl: setvar l
  let vt: setvar t
  let cI: class I
  let cJ: class J
  let cK: class K
  let cU: class U
  let cW: class W
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  assume decpmatmul.p: |- P = ( Poly1 ` R )
  assume decpmatmul.c: |- C = ( N Mat P )
  assume decpmatmul.b: |- B = ( Base ` C )
  assume decpmatmul.a: |- A = ( N Mat R )
  assume decpmatmulsumfsupp.m: |- .x. = ( .r ` A )
  assume decpmatmulsumfsupp.0: |- .0. = ( 0g ` A )

  disjoint B k
  disjoint k l
  disjoint N k
  disjoint P k
  disjoint R k
  disjoint R l
  disjoint A k
  disjoint B x
  disjoint B y
  disjoint k x
  disjoint k y
  disjoint x y
  disjoint N x
  disjoint N y
  disjoint R x
  disjoint R y
  disjoint A l
  disjoint B l
  disjoint N l
  disjoint l x
  disjoint l y
  disjoint .x. l
  disjoint B t
  disjoint k t
  disjoint I k
  disjoint I l
  disjoint I t
  disjoint l t
  disjoint J k
  disjoint J l
  disjoint J t
  disjoint K k
  disjoint K l
  disjoint K t
  disjoint N t
  disjoint P t
  disjoint R t
  disjoint U k
  disjoint U l
  disjoint U t
  disjoint W k
  disjoint W l
  disjoint W t
  disjoint A i
  disjoint A j
  disjoint i j
  disjoint i k
  disjoint j k
  disjoint B i
  disjoint B j
  disjoint i t
  disjoint i x
  disjoint i y
  disjoint j t
  disjoint j x
  disjoint j y
  disjoint t x
  disjoint t y
  disjoint C i
  disjoint C j
  disjoint K i
  disjoint K j
  disjoint K x
  disjoint K y
  disjoint N i
  disjoint N j
  disjoint R i
  disjoint R j
  disjoint U i
  disjoint U j
  disjoint U x
  disjoint U y
  disjoint W i
  disjoint W j
  disjoint W x
  disjoint W y
  disjoint A n
  disjoint A s
  disjoint k n
  disjoint k s
  disjoint l n
  disjoint l s
  disjoint n s
  disjoint B a
  disjoint B b
  disjoint B n
  disjoint a b
  disjoint a i
  disjoint a j
  disjoint a n
  disjoint b i
  disjoint b j
  disjoint b n
  disjoint i n
  disjoint j n
  disjoint B s
  disjoint C a
  disjoint C b
  disjoint C n
  disjoint C s
  disjoint a s
  disjoint b s
  disjoint N a
  disjoint N b
  disjoint N n
  disjoint N s
  disjoint R a
  disjoint R b
  disjoint R n
  disjoint R s
  disjoint a x
  disjoint b x
  disjoint n x
  disjoint a y
  disjoint b y
  disjoint n y
  disjoint s x
  disjoint s y
  disjoint .0. n
  disjoint .0. s
  disjoint .x. n
  disjoint .x. s
  assert |- ( ( ( N e. Fin /\ R e. Ring ) /\ ( x e. B /\ y e. B ) ) -> ( l e. NN0 |-> ( A gsum ( k e. ( 0 ... l ) |-> ( ( x decompPMat k ) .x. ( y decompPMat ( l - k ) ) ) ) ) ) finSupp .0. )

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
    cB
    wcel
    #
    vy
    cv
    #
    cB
    wcel
    #
    wa
    #
    wa
    #
    vn
    cvv
    cA
    vk
    cc0
    vl
    cv
    #
    cfz
    co
    #
    @3
    vk
    cv
    #
    cdecpmat
    co
    #
    @5
    @9
    @11
    cmin
    co
    #
    cdecpmat
    co
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    cA
    vk
    cc0
    vn
    cv
    #
    cfz
    co
    #
    @12
    @5
    @17
    @11
    cmin
    co
    #
    cdecpmat
    co
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    vl
    cvv
    c.0
    vs
    c.0
    cvv
    wcel
    @8
    c.0
    cA
    c0g
    cfv
    #
    cvv
    decpmatmulsumfsupp.0
    cA
    c0g
    fvex
    eqeltri
    a1i
    @8
    @9
    cn0
    wcel
    wa
    cA
    @16
    cgsu
    ovexd
    @9
    @17
    wceq
    #
    @16
    @22
    cA
    cgsu
    @25
    vk
    @10
    @15
    @18
    @21
    @9
    @17
    cc0
    cfz
    oveq2
    @25
    @14
    @20
    @12
    c.x
    @25
    @13
    @19
    @5
    cdecpmat
    @9
    @17
    @11
    cmin
    oveq1
    oveq2d
    oveq2d
    mpteq12dv
    oveq2d
    @8
    vs
    cv
    @17
    clt
    wbr
    #
    @23
    c.0
    wceq
    #
    wi
    #
    vn
    cn0
    wral
    #
    vs
    cn0
    wrex
    @26
    vi
    vj
    cN
    cN
    @17
    vi
    cv
    #
    vj
    cv
    #
    @3
    @5
    cC
    cmulr
    cfv
    #
    co
    #
    co
    #
    cco1
    cfv
    #
    cfv
    #
    cmpt2
    #
    c.0
    wceq
    #
    wi
    #
    vn
    cn0
    wral
    #
    vs
    cn0
    wrex
    #
    @8
    @26
    @17
    va
    cv
    #
    vb
    cv
    #
    @33
    co
    #
    cco1
    cfv
    #
    cfv
    #
    cR
    c0g
    cfv
    #
    wceq
    #
    vb
    cN
    wral
    va
    cN
    wral
    #
    wi
    #
    vn
    cn0
    wral
    #
    vs
    cn0
    wrex
    #
    @41
    @8
    @0
    @1
    @33
    cB
    wcel
    #
    @52
    @0
    @1
    @7
    simpll
    @0
    @1
    @7
    simplr
    @8
    cC
    crg
    wcel
    #
    @4
    @6
    w3a
    #
    @53
    @8
    @54
    @7
    wa
    @55
    @2
    @54
    @7
    cC
    cP
    cR
    cN
    decpmatmul.p
    decpmatmul.c
    pmatring
    anim1i
    @54
    @4
    @6
    3anass
    sylibr
    cB
    cC
    @32
    @3
    @5
    decpmatmul.b
    @32
    eqid
    ringcl
    syl
    #
    vn
    cB
    cC
    cP
    cR
    va
    vb
    @33
    cN
    @47
    vs
    decpmatmul.p
    decpmatmul.c
    decpmatmul.b
    @47
    eqid
    #
    pmatcoe1fsupp
    syl3anc
    @8
    @51
    @40
    vs
    cn0
    @8
    @50
    @39
    vn
    cn0
    @8
    @17
    cn0
    wcel
    #
    wa
    #
    @49
    @38
    @26
    @59
    @49
    @38
    @59
    @49
    wa
    #
    @37
    vi
    vj
    cN
    cN
    @47
    cmpt2
    #
    c.0
    @60
    vi
    vj
    cN
    cN
    @36
    @47
    @60
    @30
    cN
    wcel
    #
    @31
    cN
    wcel
    #
    @36
    @47
    wceq
    #
    @49
    @62
    @63
    wa
    #
    @64
    wi
    @59
    @65
    @49
    @64
    @48
    @64
    @17
    @30
    @43
    @33
    co
    #
    cco1
    cfv
    #
    cfv
    #
    @47
    wceq
    va
    vb
    @30
    @31
    cN
    cN
    @42
    @30
    wceq
    #
    @46
    @68
    @47
    @69
    @17
    @45
    @67
    @69
    @44
    @66
    cco1
    @42
    @30
    @43
    @33
    oveq1
    fveq2d
    fveq1d
    eqeq1d
    @43
    @31
    wceq
    #
    @68
    @36
    @47
    @70
    @17
    @67
    @35
    @70
    @66
    @34
    cco1
    @43
    @31
    @30
    @33
    oveq2
    fveq2d
    fveq1d
    eqeq1d
    rspc2va
    expcom
    adantl
    3impib
    mpt2eq3dva
    @2
    c.0
    @61
    wceq
    @7
    @58
    @49
    @2
    c.0
    @24
    @61
    decpmatmulsumfsupp.0
    cA
    cR
    vi
    vj
    cN
    @47
    decpmatmul.a
    @57
    mat0op
    syl5eq
    ad3antrrr
    eqtr4d
    ex
    imim2d
    ralimdva
    reximdv
    mpd
    @8
    @29
    @40
    vs
    cn0
    @8
    @28
    @39
    vn
    cn0
    @59
    @27
    @38
    @26
    @59
    @23
    @37
    c.0
    @59
    @23
    cA
    vk
    @18
    @12
    @20
    cA
    cmulr
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @33
    @17
    cdecpmat
    co
    #
    @37
    @59
    @22
    @73
    cA
    cgsu
    @59
    vk
    @18
    @21
    @72
    @21
    @72
    wceq
    @59
    c.x
    @71
    @12
    @20
    decpmatmulsumfsupp.m
    oveqi
    a1i
    mpteq2dv
    oveq2d
    @59
    @1
    @7
    @58
    @75
    @74
    wceq
    @0
    @1
    @7
    @58
    simpllr
    @2
    @7
    @58
    simplr
    @8
    @58
    simpr
    cA
    cB
    cC
    cP
    cR
    @3
    vk
    @17
    cN
    @5
    decpmatmul.p
    decpmatmul.c
    decpmatmul.b
    decpmatmul.a
    decpmatmul
    syl3anc
    @8
    @53
    @58
    @75
    @37
    wceq
    @56
    cC
    cB
    cP
    vi
    vj
    @17
    @33
    cN
    decpmatmul.c
    decpmatmul.b
    decpmatval
    sylan
    3eqtr2d
    eqeq1d
    imbi2d
    ralbidva
    rexbidv
    mpbird
    mptnn0fsuppd
end
