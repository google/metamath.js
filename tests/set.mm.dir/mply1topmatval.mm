include "wcel.mm"
include "wa.mm"
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
include "simpr.mm"
include "simpl.mm"
include "mpt2exga.mm"
include "syldan.mm"
include "fvmptd.mm"

theorem mply1topmatval
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
  let cV: class V
  let cY: class Y
  let vp: setvar p
  assume mply1topmat.a: |- A = ( N Mat R )
  assume mply1topmat.q: |- Q = ( Poly1 ` A )
  assume mply1topmat.l: |- L = ( Base ` Q )
  assume mply1topmat.p: |- P = ( Poly1 ` R )
  assume mply1topmat.m: |- .x. = ( .s ` P )
  assume mply1topmat.e: |- E = ( .g ` ( mulGrp ` P ) )
  assume mply1topmat.y: |- Y = ( var1 ` R )
  assume mply1topmat.i: |- I = ( p e. L |-> ( i e. N , j e. N |-> ( P gsum ( k e. NN0 |-> ( ( i ( ( coe1 ` p ) ` k ) j ) .x. ( k E Y ) ) ) ) ) )

  disjoint N i
  disjoint N j
  disjoint N p
  disjoint i j
  disjoint i p
  disjoint j p
  disjoint E p
  disjoint L p
  disjoint P p
  disjoint V p
  disjoint Y p
  disjoint O i
  disjoint O j
  disjoint O k
  disjoint O p
  disjoint i k
  disjoint j k
  disjoint k p
  disjoint .x. k
  disjoint .x. p
  assert |- ( ( N e. V /\ O e. L ) -> ( I ` O ) = ( i e. N , j e. N |-> ( P gsum ( k e. NN0 |-> ( ( i ( ( coe1 ` O ) ` k ) j ) .x. ( k E Y ) ) ) ) ) )

  proof
    cN
    cV
    wcel
    #
    cO
    cL
    wcel
    #
    wa
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
    @5
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
    @3
    @4
    @5
    cO
    cco1
    cfv
    #
    cfv
    #
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
    cmpt2
    #
    cL
    cI
    cvv
    cI
    vp
    cL
    @14
    cmpt
    wceq
    @2
    mply1topmat.i
    a1i
    @6
    cO
    wceq
    #
    @14
    @21
    wceq
    @2
    @22
    vi
    vj
    cN
    cN
    @13
    @20
    @22
    @12
    @19
    cP
    cgsu
    @22
    vk
    cn0
    @11
    @18
    @22
    @9
    @17
    @10
    c.x
    @22
    @8
    @16
    @3
    @4
    @22
    @5
    @7
    @15
    @6
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
    simpr
    @0
    @1
    @0
    @21
    cvv
    wcel
    @0
    @1
    simpl
    vi
    vj
    cN
    cN
    @20
    cV
    cV
    mpt2exga
    syldan
    fvmptd
end
