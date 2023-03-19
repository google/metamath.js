include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "w3a.mm"
include "cfv.mm"
include "cn0.mm"
include "cv.mm"
include "cdecpmat.mm"
include "co.mm"
include "cv1.mm"
include "cmgp.mm"
include "cmg.mm"
include "cvsca.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cmat.mm"
include "cbs.mm"
include "wceq.mm"
include "eqid.mm"
include "mply1topmatcl.mm"
include "pm2mpfval.mm"
include "syld3an3.mm"
include "cco1.mm"
include "wral.mm"
include "matring.mm"
include "3adant3.mm"
include "cvv.mm"
include "c0g.mm"
include "ccmn.mm"
include "wa.mm"
include "ply1ring.mm"
include "ringcmn.mm"
include "3syl.mm"
include "nn0ex.mm"
include "a1i.mm"
include "adantr.mm"
include "simpl2.mm"
include "simpr.mm"
include "decpmatcl.mm"
include "syl3anc.mm"
include "ply1tmcl.mm"
include "fmptd.mm"
include "cmpt2.mm"
include "fveq2.mm"
include "oveqd.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "cbvmptv.mm"
include "oveq2d.mm"
include "mpt2eq3ia.mm"
include "mpteq2i.mm"
include "eqtri.mm"
include "mp2pm2mplem5.mm"
include "gsumcl.mm"
include "simp3.mm"
include "3jca.mm"
include "mp2pm2mplem4.mm"
include "oveq1d.mm"
include "adantlr.mm"
include "mpteq2dva.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "jca.mm"
include "ply1coe.mm"
include "syl.mm"
include "eqcomd.mm"
include "eqtrd.mm"
include "ralrimiva.mm"
include "eqcoe1ply1eq.mm"
include "sylc.mm"

theorem mp2pm2mp
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cT: class T
  let c.x: class .x.
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cE: class E
  let cI: class I
  let cL: class L
  let cN: class N
  let cO: class O
  let cY: class Y
  let vp: setvar p
  let cK: class K
  let va: setvar a
  let vb: setvar b
  let vn: setvar n
  let vl: setvar l
  assume mp2pm2mp.a: |- A = ( N Mat R )
  assume mp2pm2mp.q: |- Q = ( Poly1 ` A )
  assume mp2pm2mp.l: |- L = ( Base ` Q )
  assume mp2pm2mp.m: |- .x. = ( .s ` P )
  assume mp2pm2mp.e: |- E = ( .g ` ( mulGrp ` P ) )
  assume mp2pm2mp.y: |- Y = ( var1 ` R )
  assume mp2pm2mp.i: |- I = ( p e. L |-> ( i e. N , j e. N |-> ( P gsum ( k e. NN0 |-> ( ( i ( ( coe1 ` p ) ` k ) j ) .x. ( k E Y ) ) ) ) ) )
  assume mp2pm2mplem2.p: |- P = ( Poly1 ` R )
  assume mp2pm2mp.t: |- T = ( N pMatToMatPoly R )

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
  disjoint A i
  disjoint A j
  disjoint A k
  disjoint E k
  disjoint Y k
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
  disjoint A n
  disjoint i n
  disjoint j n
  disjoint k n
  disjoint A l
  disjoint E n
  disjoint n p
  disjoint I l
  disjoint I n
  disjoint l n
  disjoint L l
  disjoint L n
  disjoint N l
  disjoint N n
  disjoint O l
  disjoint O n
  disjoint P n
  disjoint Q l
  disjoint Q n
  disjoint R l
  disjoint R n
  disjoint Y n
  disjoint .x. n
  assert |- ( ( N e. Fin /\ R e. Ring /\ O e. L ) -> ( T ` ( I ` O ) ) = O )

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
    cO
    cI
    cfv
    #
    cT
    cfv
    #
    cQ
    vn
    cn0
    @4
    vn
    cv
    #
    cdecpmat
    co
    #
    @6
    cA
    cv1
    cfv
    #
    cQ
    cmgp
    cfv
    #
    cmg
    cfv
    #
    co
    #
    cQ
    cvsca
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cO
    @0
    @1
    @2
    @4
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
    @5
    @15
    wceq
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
    #
    cA
    @17
    @16
    cP
    cQ
    cR
    cT
    vn
    @10
    @12
    @4
    cN
    crg
    @8
    mp2pm2mplem2.p
    @19
    @20
    @12
    eqid
    #
    @10
    eqid
    #
    @8
    eqid
    #
    mp2pm2mp.a
    mp2pm2mp.q
    mp2pm2mp.t
    pm2mpfval
    syld3an3
    @3
    cA
    crg
    wcel
    #
    @15
    cL
    wcel
    #
    @2
    w3a
    vl
    cv
    #
    @15
    cco1
    cfv
    #
    cfv
    #
    @27
    cO
    cco1
    cfv
    #
    cfv
    #
    wceq
    #
    vl
    cn0
    wral
    @15
    cO
    wceq
    @3
    @25
    @26
    @2
    @0
    @1
    @25
    @2
    cA
    cR
    cN
    mp2pm2mp.a
    matring
    #
    3adant3
    #
    @3
    cn0
    cL
    @14
    cQ
    cvv
    cQ
    c0g
    cfv
    #
    mp2pm2mp.l
    @35
    eqid
    @0
    @1
    cQ
    ccmn
    wcel
    #
    @2
    @0
    @1
    wa
    @25
    cQ
    crg
    wcel
    @36
    @33
    cQ
    cA
    mp2pm2mp.q
    ply1ring
    cQ
    ringcmn
    3syl
    3adant3
    cn0
    cvv
    wcel
    @3
    nn0ex
    a1i
    @3
    vn
    cn0
    @13
    cL
    @14
    @3
    @6
    cn0
    wcel
    #
    wa
    #
    @25
    @7
    cA
    cbs
    cfv
    #
    wcel
    #
    @37
    @13
    cL
    wcel
    @3
    @25
    @37
    @34
    adantr
    @38
    @1
    @18
    @37
    @40
    @0
    @1
    @2
    @37
    simpl2
    @3
    @18
    @37
    @21
    adantr
    @3
    @37
    simpr
    #
    cA
    @17
    @16
    @39
    cP
    cR
    @6
    @4
    cN
    crg
    mp2pm2mplem2.p
    @19
    @20
    mp2pm2mp.a
    @39
    eqid
    #
    decpmatcl
    syl3anc
    @41
    cL
    @7
    @6
    cQ
    cA
    @12
    @10
    @39
    @9
    @8
    @42
    mp2pm2mp.q
    @24
    @22
    @9
    eqid
    #
    @23
    mp2pm2mp.l
    ply1tmcl
    syl3anc
    @14
    eqid
    fmptd
    cA
    cP
    cQ
    cR
    c.x
    vi
    vj
    vn
    cE
    @10
    cI
    @12
    cL
    cN
    cO
    @8
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
    vk
    cv
    #
    vp
    cv
    cco1
    cfv
    #
    cfv
    #
    co
    #
    @46
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
    vn
    cn0
    @44
    @45
    @6
    @47
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
    mp2pm2mp.i
    vp
    cL
    @54
    @61
    vi
    vj
    cN
    cN
    @53
    @60
    @44
    cN
    wcel
    @45
    cN
    wcel
    wa
    #
    @52
    @59
    cP
    cgsu
    @52
    @59
    wceq
    @62
    vk
    vn
    cn0
    @51
    @58
    @46
    @6
    wceq
    #
    @49
    @56
    @50
    @57
    c.x
    @63
    @48
    @55
    @44
    @45
    @46
    @6
    @47
    fveq2
    oveqd
    @46
    @6
    cY
    cE
    oveq1
    oveq12d
    cbvmptv
    a1i
    oveq2d
    mpt2eq3ia
    mpteq2i
    eqtri
    mp2pm2mplem2.p
    @22
    @23
    @24
    mp2pm2mplem5
    gsumcl
    @0
    @1
    @2
    simp3
    #
    3jca
    @3
    @32
    vl
    cn0
    @3
    @27
    cn0
    wcel
    #
    wa
    #
    @29
    @27
    cQ
    vn
    cn0
    @6
    @30
    cfv
    #
    @11
    @12
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
    @31
    @66
    @27
    @28
    @71
    @66
    @15
    @70
    cco1
    @66
    @14
    @69
    cQ
    cgsu
    @66
    vn
    cn0
    @13
    @68
    @3
    @37
    @13
    @68
    wceq
    @65
    @38
    @7
    @67
    @11
    @12
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
    mp2pm2mp.i
    mp2pm2mplem2.p
    mp2pm2mplem4
    oveq1d
    adantlr
    mpteq2dva
    oveq2d
    fveq2d
    fveq1d
    @66
    @27
    @71
    @30
    @66
    @70
    cO
    cco1
    @66
    cO
    @70
    @66
    @25
    @2
    wa
    #
    cO
    @70
    wceq
    @3
    @72
    @65
    @3
    @25
    @2
    @34
    @64
    jca
    adantr
    @30
    cL
    cQ
    cA
    @12
    vn
    @10
    cO
    @9
    @8
    mp2pm2mp.q
    @24
    mp2pm2mp.l
    @22
    @43
    @23
    @30
    eqid
    #
    ply1coe
    syl
    eqcomd
    fveq2d
    fveq1d
    eqtrd
    ralrimiva
    @28
    cL
    @30
    cQ
    cA
    vl
    @15
    cO
    mp2pm2mp.q
    mp2pm2mp.l
    @28
    eqid
    @73
    eqcoe1ply1eq
    sylc
    eqtrd
end
