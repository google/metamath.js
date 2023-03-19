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
include "cmpt2.mm"
include "cvv.mm"
include "wceq.mm"
include "a1i.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "oveqd.mm"
include "oveq1d.mm"
include "mpteq2dv.mm"
include "oveq2d.mm"
include "mpt2eq3dv.mm"
include "adantl.mm"
include "simp3.mm"
include "simp1.mm"
include "mpt2exga.mm"
include "syl2anc.mm"
include "fvmptd.mm"

theorem mp2pm2mplem1
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
  assert |- ( ( N e. Fin /\ R e. Ring /\ O e. L ) -> ( I ` O ) = ( i e. N , j e. N |-> ( P gsum ( k e. NN0 |-> ( ( i ( ( coe1 ` O ) ` k ) j ) .x. ( k E Y ) ) ) ) ) )

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
    vp
    cO
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
    #
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
    vi
    vj
    cN
    cN
    cP
    vk
    cn0
    @4
    @5
    @6
    cO
    cco1
    cfv
    #
    cfv
    #
    co
    #
    @11
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
    cL
    cI
    cvv
    cI
    vp
    cL
    @15
    cmpt
    wceq
    @3
    mp2pm2mp.i
    a1i
    @7
    cO
    wceq
    #
    @15
    @22
    wceq
    @3
    @23
    vi
    vj
    cN
    cN
    @14
    @21
    @23
    @13
    @20
    cP
    cgsu
    @23
    vk
    cn0
    @12
    @19
    @23
    @10
    @18
    @11
    c.x
    @23
    @9
    @17
    @4
    @5
    @23
    @6
    @8
    @16
    @7
    cO
    cco1
    fveq2
    fveq1d
    oveqd
    oveq1d
    mpteq2dv
    oveq2d
    mpt2eq3dv
    adantl
    @0
    @1
    @2
    simp3
    @3
    @0
    @0
    @22
    cvv
    wcel
    @0
    @1
    @2
    simp1
    #
    @24
    vi
    vj
    cN
    cN
    @21
    cfn
    cfn
    mpt2exga
    syl2anc
    fvmptd
end
