include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "w3a.mm"
include "cn0.mm"
include "cv.mm"
include "cco1.mm"
include "cfv.mm"
include "co.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cbs.mm"
include "eqid.mm"
include "simp1.mm"
include "ply1ring.mm"
include "3ad2ant2.mm"
include "cvv.mm"
include "c0g.mm"
include "ccmn.mm"
include "ringcmn.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "nn0ex.mm"
include "a1i.mm"
include "wa.mm"
include "simpl12.mm"
include "simpl2.mm"
include "simpl3.mm"
include "simp13.mm"
include "coe1fvalcl.mm"
include "sylan.mm"
include "matecld.mm"
include "simpr.mm"
include "cmgp.mm"
include "ply1tmcl.mm"
include "syl3anc.mm"
include "fmptd.mm"
include "mply1topmatcllem.mm"
include "gsumcl.mm"
include "matbas2d.mm"

theorem mp2pm2mplem2
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
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
  assume mp2pm2mp.a: |- A = ( N Mat R )
  assume mp2pm2mp.q: |- Q = ( Poly1 ` A )
  assume mp2pm2mp.l: |- L = ( Base ` Q )
  assume mp2pm2mp.m: |- .x. = ( .s ` P )
  assume mp2pm2mp.e: |- E = ( .g ` ( mulGrp ` P ) )
  assume mp2pm2mp.y: |- Y = ( var1 ` R )
  assume mp2pm2mp.i: |- I = ( p e. L |-> ( i e. N , j e. N |-> ( P gsum ( k e. NN0 |-> ( ( i ( ( coe1 ` p ) ` k ) j ) .x. ( k E Y ) ) ) ) ) )
  assume mp2pm2mplem2.p: |- P = ( Poly1 ` R )
  assume mp2pm2mplem2.c: |- C = ( N Mat P )
  assume mp2pm2mplem2.b: |- B = ( Base ` C )

  disjoint L i
  disjoint L j
  disjoint L k
  disjoint i j
  disjoint i k
  disjoint j k
  disjoint N k
  disjoint R i
  disjoint R j
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
  assert |- ( ( N e. Fin /\ R e. Ring /\ O e. L ) -> ( i e. N , j e. N |-> ( P gsum ( k e. NN0 |-> ( ( i ( ( coe1 ` O ) ` k ) j ) .x. ( k E Y ) ) ) ) ) e. B )

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
    vi
    vj
    cC
    cB
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
    #
    cfv
    #
    co
    #
    @6
    cY
    cE
    co
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    cP
    cP
    cbs
    cfv
    #
    cN
    crg
    mp2pm2mplem2.c
    @12
    eqid
    #
    mp2pm2mplem2.b
    @0
    @1
    @2
    simp1
    @1
    @0
    cP
    crg
    wcel
    #
    @2
    cP
    cR
    mp2pm2mplem2.p
    ply1ring
    #
    3ad2ant2
    @3
    @4
    cN
    wcel
    #
    @5
    cN
    wcel
    #
    w3a
    #
    cn0
    @12
    @11
    cP
    cvv
    cP
    c0g
    cfv
    #
    @13
    @19
    eqid
    @3
    @16
    cP
    ccmn
    wcel
    #
    @17
    @1
    @0
    @20
    @2
    @1
    @14
    @20
    @15
    cP
    ringcmn
    syl
    3ad2ant2
    3ad2ant1
    cn0
    cvv
    wcel
    @18
    nn0ex
    a1i
    @18
    vk
    cn0
    @10
    @12
    @11
    @18
    @6
    cn0
    wcel
    #
    wa
    #
    @1
    @9
    cR
    cbs
    cfv
    #
    wcel
    @21
    @10
    @12
    wcel
    @0
    @1
    @2
    @16
    @17
    @21
    simpl12
    @22
    cA
    cA
    cbs
    cfv
    #
    cR
    @4
    @5
    @23
    @8
    cN
    mp2pm2mp.a
    @23
    eqid
    #
    @24
    eqid
    #
    @3
    @16
    @17
    @21
    simpl2
    @3
    @16
    @17
    @21
    simpl3
    @18
    @2
    @21
    @8
    @24
    wcel
    @0
    @1
    @2
    @16
    @17
    simp13
    @7
    cL
    cQ
    cA
    cO
    @24
    @6
    @7
    eqid
    mp2pm2mp.l
    mp2pm2mp.q
    @26
    coe1fvalcl
    sylan
    matecld
    @18
    @21
    simpr
    @12
    @9
    @6
    cP
    cR
    c.x
    cE
    @23
    cP
    cmgp
    cfv
    #
    cY
    @25
    mp2pm2mplem2.p
    mp2pm2mp.y
    mp2pm2mp.m
    @27
    eqid
    mp2pm2mp.e
    @13
    ply1tmcl
    syl3anc
    @11
    eqid
    fmptd
    cA
    cP
    cQ
    cR
    c.x
    vk
    cE
    @4
    @5
    cL
    cN
    cO
    cY
    mp2pm2mp.a
    mp2pm2mp.q
    mp2pm2mp.l
    mp2pm2mplem2.p
    mp2pm2mp.m
    mp2pm2mp.e
    mp2pm2mp.y
    mply1topmatcllem
    gsumcl
    matbas2d
end
