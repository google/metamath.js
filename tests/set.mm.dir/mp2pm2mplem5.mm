include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "w3a.mm"
include "cbs.mm"
include "cfv.mm"
include "cn0.mm"
include "cv.mm"
include "cdecpmat.mm"
include "co.mm"
include "cvv.mm"
include "c0g.mm"
include "nn0ex.mm"
include "a1i.mm"
include "clmod.mm"
include "wa.mm"
include "matring.mm"
include "ply1lmod.mm"
include "syl.mm"
include "3adant3.mm"
include "csca.mm"
include "wceq.mm"
include "ply1sca.mm"
include "cmat.mm"
include "simpl2.mm"
include "eqid.mm"
include "mply1topmatcl.mm"
include "adantr.mm"
include "simpr.mm"
include "decpmatcl.mm"
include "syl3anc.mm"
include "cmgp.mm"
include "ply1moncl.mm"
include "sylan.mm"
include "cmpt.mm"
include "cco1.mm"
include "cfsupp.mm"
include "cgsu.mm"
include "cmpt2.mm"
include "fveq2.mm"
include "oveqd.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "cbvmptv.mm"
include "oveq2i.mm"
include "mpt2eq3ia.mm"
include "mpteq2i.mm"
include "eqtri.mm"
include "mp2pm2mplem4.mm"
include "mpteq2dva.mm"
include "wbr.mm"
include "mptcoe1fsupp.mm"
include "stoic3.mm"
include "eqbrtrd.mm"
include "mptscmfsupp0.mm"

theorem mp2pm2mplem5
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.x: class .x.
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cE: class E
  let c.ex: class .^
  let cI: class I
  let c.as: class .*
  let cL: class L
  let cN: class N
  let cO: class O
  let cX: class X
  let cY: class Y
  let vp: setvar p
  let vs: setvar s
  let vx: setvar x
  let vl: setvar l
  let cK: class K
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
  assume mp2pm2mplem5.m: |- .* = ( .s ` Q )
  assume mp2pm2mplem5.e: |- .^ = ( .g ` ( mulGrp ` Q ) )
  assume mp2pm2mplem5.x: |- X = ( var1 ` A )

  disjoint A i
  disjoint A j
  disjoint A k
  disjoint i j
  disjoint i k
  disjoint j k
  disjoint E k
  disjoint Y k
  disjoint .* k
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
  disjoint L i
  disjoint L j
  disjoint N k
  disjoint R i
  disjoint R j
  disjoint Y i
  disjoint Y j
  disjoint .x. i
  disjoint .x. j
  disjoint A s
  disjoint A x
  disjoint i s
  disjoint i x
  disjoint j s
  disjoint j x
  disjoint k s
  disjoint k x
  disjoint s x
  disjoint E s
  disjoint E x
  disjoint E l
  disjoint K k
  disjoint K s
  disjoint K x
  disjoint K l
  disjoint L l
  disjoint L s
  disjoint L x
  disjoint N l
  disjoint N s
  disjoint l s
  disjoint N x
  disjoint O l
  disjoint O s
  disjoint O x
  disjoint P l
  disjoint P s
  disjoint P x
  disjoint R l
  disjoint R s
  disjoint R x
  disjoint Y l
  disjoint Y s
  disjoint Y x
  disjoint .x. l
  disjoint .x. s
  disjoint .x. x
  disjoint a b
  disjoint a s
  disjoint b s
  disjoint i l
  disjoint j l
  disjoint k l
  disjoint A l
  disjoint l p
  disjoint K a
  disjoint K b
  disjoint K i
  disjoint K j
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
  assert |- ( ( N e. Fin /\ R e. Ring /\ O e. L ) -> ( k e. NN0 |-> ( ( ( I ` O ) decompPMat k ) .* ( k .^ X ) ) ) finSupp ( 0g ` Q ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    cO
    cL
    wcel
    #
    w3a
    #
    cA
    cbs
    cfv
    #
    cn0
    cQ
    cA
    cO
    cI
    cfv
    #
    vk
    cv
    #
    cdecpmat
    co
    #
    vk
    c.as
    cL
    cvv
    @6
    cX
    c.ex
    co
    #
    cQ
    c0g
    cfv
    #
    cA
    c0g
    cfv
    #
    cn0
    cvv
    wcel
    @3
    nn0ex
    a1i
    @0
    @1
    cQ
    clmod
    wcel
    #
    @2
    @0
    @1
    wa
    cA
    crg
    wcel
    #
    @11
    cA
    cR
    cN
    mp2pm2mp.a
    matring
    #
    cQ
    cA
    mp2pm2mp.q
    ply1lmod
    syl
    3adant3
    @3
    @12
    cA
    cQ
    csca
    cfv
    wceq
    @0
    @1
    @12
    @2
    @13
    3adant3
    #
    cQ
    cA
    crg
    mp2pm2mp.q
    ply1sca
    syl
    mp2pm2mp.l
    @3
    @6
    cn0
    wcel
    #
    wa
    @1
    @5
    cN
    cP
    cmat
    co
    #
    cbs
    cfv
    #
    wcel
    #
    @15
    @7
    @4
    wcel
    @0
    @1
    @2
    @15
    simpl2
    @3
    @18
    @15
    cA
    @17
    @16
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
    mp2pm2mplem2.p
    mp2pm2mp.m
    mp2pm2mp.e
    mp2pm2mp.y
    mp2pm2mp.i
    @16
    eqid
    #
    @17
    eqid
    #
    mply1topmatcl
    adantr
    @3
    @15
    simpr
    cA
    @17
    @16
    @4
    cP
    cR
    @6
    @5
    cN
    crg
    mp2pm2mplem2.p
    @19
    @20
    mp2pm2mp.a
    @4
    eqid
    decpmatcl
    syl3anc
    @3
    @12
    @15
    @8
    cL
    wcel
    @14
    cL
    @6
    cQ
    cA
    c.ex
    cQ
    cmgp
    cfv
    #
    cX
    mp2pm2mp.q
    mp2pm2mplem5.x
    @21
    eqid
    mp2pm2mplem5.e
    mp2pm2mp.l
    ply1moncl
    sylan
    @9
    eqid
    @10
    eqid
    #
    mp2pm2mplem5.m
    @3
    vk
    cn0
    @7
    cmpt
    vk
    cn0
    @6
    cO
    cco1
    cfv
    cfv
    #
    cmpt
    #
    @10
    cfsupp
    @3
    vk
    cn0
    @7
    @23
    cA
    cP
    cQ
    cR
    c.x
    vi
    vj
    vl
    cE
    cI
    @6
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
    cI
    vp
    cL
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
    @6
    vp
    cv
    cco1
    cfv
    #
    cfv
    #
    co
    #
    @6
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
    cmpt
    vp
    cL
    vi
    vj
    cN
    cN
    cP
    vl
    cn0
    @25
    @26
    vl
    cv
    #
    @27
    cfv
    #
    co
    #
    @35
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
    cmpt
    mp2pm2mp.i
    vp
    cL
    @34
    @42
    vi
    vj
    cN
    cN
    @33
    @41
    @33
    @41
    wceq
    @25
    cN
    wcel
    @26
    cN
    wcel
    wa
    @32
    @40
    cP
    cgsu
    vk
    vl
    cn0
    @31
    @39
    @6
    @35
    wceq
    #
    @29
    @37
    @30
    @38
    c.x
    @43
    @28
    @36
    @25
    @26
    @6
    @35
    @27
    fveq2
    oveqd
    @6
    @35
    cY
    cE
    oveq1
    oveq12d
    cbvmptv
    oveq2i
    a1i
    mpt2eq3ia
    mpteq2i
    eqtri
    mp2pm2mplem2.p
    mp2pm2mplem4
    mpteq2dva
    @0
    @1
    @12
    @2
    @24
    @10
    cfsupp
    wbr
    @13
    cL
    cQ
    cA
    vk
    cO
    @10
    mp2pm2mp.q
    mp2pm2mp.l
    @22
    mptcoe1fsupp
    stoic3
    eqbrtrd
    mptscmfsupp0
end
