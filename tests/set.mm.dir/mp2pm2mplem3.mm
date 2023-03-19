include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "w3a.mm"
include "cn0.mm"
include "wa.mm"
include "cfv.mm"
include "cdecpmat.mm"
include "co.mm"
include "cv.mm"
include "cco1.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cmpt2.mm"
include "wceq.mm"
include "mp2pm2mplem1.mm"
include "oveq1d.mm"
include "adantr.mm"
include "cmat.mm"
include "cbs.mm"
include "eqid.mm"
include "mp2pm2mplem2.mm"
include "decpmatval.mm"
include "sylan.mm"
include "cvv.mm"
include "eqidd.mm"
include "weq.mm"
include "oveq12.mm"
include "mpteq2dv.mm"
include "oveq2d.mm"
include "adantl.mm"
include "simp2.mm"
include "simp3.mm"
include "ovexd.mm"
include "ovmpt2d.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "mpt2eq3dva.mm"
include "oveq1.mm"
include "simpl.mm"
include "mpteq2dva.mm"
include "cbvmpt2v.mm"
include "syl6eq.mm"
include "3eqtrd.mm"

theorem mp2pm2mplem3
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.x: class .x.
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cE: class E
  let cI: class I
  let cK: class K
  let cL: class L
  let cN: class N
  let cO: class O
  let cY: class Y
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  assume mp2pm2mp.a: |- A = ( N Mat R )
  assume mp2pm2mp.q: |- Q = ( Poly1 ` A )
  assume mp2pm2mp.l: |- L = ( Base ` Q )
  assume mp2pm2mp.m: |- .x. = ( .s ` P )
  assume mp2pm2mp.e: |- E = ( .g ` ( mulGrp ` P ) )
  assume mp2pm2mp.y: |- Y = ( var1 ` R )
  assume mp2pm2mp.i: |- I = ( p e. L |-> ( i e. N , j e. N |-> ( P gsum ( k e. NN0 |-> ( ( i ( ( coe1 ` p ) ` k ) j ) .x. ( k E Y ) ) ) ) ) )
  assume mp2pm2mplem2.p: |- P = ( Poly1 ` R )

  disjoint N i
  disjoint N j
  disjoint N k
  disjoint i j
  disjoint i k
  disjoint j k
  disjoint E p
  disjoint L p
  disjoint N i
  disjoint N j
  disjoint N p
  disjoint i j
  disjoint i p
  disjoint j p
  disjoint O i
  disjoint O j
  disjoint O p
  disjoint O k
  disjoint k p
  disjoint P p
  disjoint R p
  disjoint Y p
  disjoint .x. p
  disjoint L k
  disjoint P i
  disjoint P j
  disjoint P k
  disjoint i k
  disjoint j k
  disjoint R k
  disjoint .x. k
  disjoint E i
  disjoint E j
  disjoint K i
  disjoint K j
  disjoint L i
  disjoint L j
  disjoint N k
  disjoint R i
  disjoint R j
  disjoint Y i
  disjoint Y j
  disjoint .x. i
  disjoint .x. j
  disjoint E a
  disjoint E b
  disjoint a b
  disjoint P a
  disjoint P b
  disjoint Y a
  disjoint Y b
  disjoint .x. a
  disjoint .x. b
  disjoint K a
  disjoint K b
  disjoint a b
  disjoint a i
  disjoint a j
  disjoint b i
  disjoint b j
  disjoint L a
  disjoint L b
  disjoint N a
  disjoint N b
  disjoint a k
  disjoint b k
  disjoint O a
  disjoint O b
  disjoint R a
  disjoint R b
  assert |- ( ( ( N e. Fin /\ R e. Ring /\ O e. L ) /\ K e. NN0 ) -> ( ( I ` O ) decompPMat K ) = ( i e. N , j e. N |-> ( ( coe1 ` ( P gsum ( k e. NN0 |-> ( ( i ( ( coe1 ` O ) ` k ) j ) .x. ( k E Y ) ) ) ) ) ` K ) ) )

  proof
    cN
    cfn
    wcel
    cR
    crg
    wcel
    cO
    cL
    wcel
    w3a
    #
    cK
    cn0
    wcel
    #
    wa
    #
    cO
    cI
    cfv
    #
    cK
    cdecpmat
    co
    #
    vi
    vj
    cN
    cN
    cP
    vk
    cn0
    vi
    cv
    #
    vj
    cv
    #
    vk
    cv
    #
    cO
    cco1
    cfv
    cfv
    #
    co
    #
    @7
    cY
    cE
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
    cmpt2
    #
    cK
    cdecpmat
    co
    #
    va
    vb
    cN
    cN
    cK
    va
    cv
    #
    vb
    cv
    #
    @14
    co
    #
    cco1
    cfv
    #
    cfv
    #
    cmpt2
    #
    vi
    vj
    cN
    cN
    cK
    @13
    cco1
    cfv
    #
    cfv
    #
    cmpt2
    #
    @0
    @4
    @15
    wceq
    @1
    @0
    @3
    @14
    cK
    cdecpmat
    cA
    cP
    cQ
    cR
    c.x
    vi
    vj
    vk
    cE
    cI
    cL
    cN
    cO
    cY
    vp
    mp2pm2mp.a
    mp2pm2mp.q
    mp2pm2mp.l
    mp2pm2mp.m
    mp2pm2mp.e
    mp2pm2mp.y
    mp2pm2mp.i
    mp2pm2mplem1
    oveq1d
    adantr
    @0
    @14
    cN
    cP
    cmat
    co
    #
    cbs
    cfv
    #
    wcel
    @1
    @15
    @21
    wceq
    cA
    @26
    @25
    cP
    cQ
    cR
    c.x
    vi
    vj
    vk
    cE
    cI
    cL
    cN
    cO
    cY
    vp
    mp2pm2mp.a
    mp2pm2mp.q
    mp2pm2mp.l
    mp2pm2mp.m
    mp2pm2mp.e
    mp2pm2mp.y
    mp2pm2mp.i
    mp2pm2mplem2.p
    @25
    eqid
    #
    @26
    eqid
    #
    mp2pm2mplem2
    @25
    @26
    cP
    va
    vb
    cK
    @14
    cN
    @27
    @28
    decpmatval
    sylan
    @2
    @21
    va
    vb
    cN
    cN
    cK
    cP
    vk
    cn0
    @16
    @17
    @8
    co
    #
    @10
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cco1
    cfv
    #
    cfv
    #
    cmpt2
    @24
    @2
    va
    vb
    cN
    cN
    @20
    @34
    @2
    @16
    cN
    wcel
    #
    @17
    cN
    wcel
    #
    w3a
    #
    cK
    @19
    @33
    @37
    @18
    @32
    cco1
    @37
    vi
    vj
    @16
    @17
    cN
    cN
    @13
    @32
    @14
    cvv
    @37
    @14
    eqidd
    vi
    va
    weq
    vj
    vb
    weq
    wa
    #
    @13
    @32
    wceq
    @37
    @38
    @12
    @31
    cP
    cgsu
    @38
    vk
    cn0
    @11
    @30
    @38
    @9
    @29
    @10
    c.x
    @5
    @16
    @6
    @17
    @8
    oveq12
    oveq1d
    mpteq2dv
    oveq2d
    adantl
    @2
    @35
    @36
    simp2
    @2
    @35
    @36
    simp3
    @37
    cP
    @31
    cgsu
    ovexd
    ovmpt2d
    fveq2d
    fveq1d
    mpt2eq3dva
    va
    vb
    vi
    vj
    cN
    cN
    @34
    @23
    cK
    cP
    vk
    cn0
    @5
    @17
    @8
    co
    #
    @10
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cco1
    cfv
    #
    cfv
    va
    vi
    weq
    #
    cK
    @33
    @43
    @44
    @32
    @42
    cco1
    @44
    @31
    @41
    cP
    cgsu
    @44
    vk
    cn0
    @30
    @40
    @44
    @29
    @39
    @10
    c.x
    @16
    @5
    @17
    @8
    oveq1
    oveq1d
    mpteq2dv
    oveq2d
    fveq2d
    fveq1d
    vb
    vj
    weq
    #
    cK
    @43
    @22
    @45
    @42
    @13
    cco1
    @45
    @41
    @12
    cP
    cgsu
    @45
    vk
    cn0
    @40
    @11
    @45
    @7
    cn0
    wcel
    #
    wa
    #
    @39
    @9
    @10
    c.x
    @47
    @17
    @6
    @5
    @8
    @45
    @46
    simpl
    oveq2d
    oveq1d
    mpteq2dva
    oveq2d
    fveq2d
    fveq1d
    cbvmpt2v
    syl6eq
    3eqtrd
end
