include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "w3a.mm"
include "cvv.mm"
include "cn0.mm"
include "cv.mm"
include "cco1.mm"
include "cfv.mm"
include "co.mm"
include "cbs.mm"
include "c0g.mm"
include "nn0ex.mm"
include "a1i.mm"
include "clmod.mm"
include "ply1lmod.mm"
include "3ad2ant2.mm"
include "3ad2ant1.mm"
include "csca.mm"
include "wceq.mm"
include "simp12.mm"
include "ply1sca.mm"
include "syl.mm"
include "eqid.mm"
include "wa.mm"
include "ovexd.mm"
include "cmgp.mm"
include "cmnd.mm"
include "ply1ring.mm"
include "ringmgp.mm"
include "adantr.mm"
include "simpr.mm"
include "vr1cl.mm"
include "mgpbas.mm"
include "mulgnn0cl.mm"
include "syl3anc.mm"
include "mptcoe1matfsupp.mm"
include "mptscmfsupp0.mm"

theorem mply1topmatcllem
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.x: class .x.
  let vk: setvar k
  let cE: class E
  let cI: class I
  let cJ: class J
  let cL: class L
  let cN: class N
  let cO: class O
  let cY: class Y
  let vi: setvar i
  let vj: setvar j
  let vp: setvar p
  let cV: class V
  assume mply1topmat.a: |- A = ( N Mat R )
  assume mply1topmat.q: |- Q = ( Poly1 ` A )
  assume mply1topmat.l: |- L = ( Base ` Q )
  assume mply1topmat.p: |- P = ( Poly1 ` R )
  assume mply1topmat.m: |- .x. = ( .s ` P )
  assume mply1topmat.e: |- E = ( .g ` ( mulGrp ` P ) )
  assume mply1topmat.y: |- Y = ( var1 ` R )

  disjoint I k
  disjoint J k
  disjoint L k
  disjoint N k
  disjoint P k
  disjoint R k
  disjoint O k
  disjoint .x. k
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
  disjoint O p
  disjoint i k
  disjoint j k
  disjoint k p
  disjoint .x. p
  assert |- ( ( ( N e. Fin /\ R e. Ring /\ O e. L ) /\ I e. N /\ J e. N ) -> ( k e. NN0 |-> ( ( I ( ( coe1 ` O ) ` k ) J ) .x. ( k E Y ) ) ) finSupp ( 0g ` P ) )

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
    cI
    cN
    wcel
    #
    cJ
    cN
    wcel
    #
    w3a
    #
    cvv
    cn0
    cP
    cR
    cI
    cJ
    vk
    cv
    #
    cO
    cco1
    cfv
    cfv
    #
    co
    vk
    c.x
    cP
    cbs
    cfv
    #
    cvv
    @7
    cY
    cE
    co
    #
    cP
    c0g
    cfv
    #
    cR
    c0g
    cfv
    #
    cn0
    cvv
    wcel
    @6
    nn0ex
    a1i
    @3
    @4
    cP
    clmod
    wcel
    #
    @5
    @1
    @0
    @13
    @2
    cP
    cR
    mply1topmat.p
    ply1lmod
    3ad2ant2
    3ad2ant1
    @6
    @1
    cR
    cP
    csca
    cfv
    wceq
    @0
    @1
    @2
    @4
    @5
    simp12
    cP
    cR
    crg
    mply1topmat.p
    ply1sca
    syl
    @9
    eqid
    #
    @6
    @7
    cn0
    wcel
    #
    wa
    #
    cI
    cJ
    @8
    ovexd
    @16
    cP
    cmgp
    cfv
    #
    cmnd
    wcel
    #
    @15
    cY
    @9
    wcel
    #
    @10
    @9
    wcel
    @6
    @18
    @15
    @3
    @4
    @18
    @5
    @1
    @0
    @18
    @2
    @1
    cP
    crg
    wcel
    @18
    cP
    cR
    mply1topmat.p
    ply1ring
    cP
    @17
    @17
    eqid
    #
    ringmgp
    syl
    3ad2ant2
    3ad2ant1
    adantr
    @6
    @15
    simpr
    @6
    @19
    @15
    @3
    @4
    @19
    @5
    @1
    @0
    @19
    @2
    @9
    cP
    cR
    cY
    mply1topmat.y
    mply1topmat.p
    @14
    vr1cl
    3ad2ant2
    3ad2ant1
    adantr
    @9
    cE
    @17
    @7
    cY
    @9
    cP
    @17
    @20
    @14
    mgpbas
    mply1topmat.e
    mulgnn0cl
    syl3anc
    @11
    eqid
    @12
    eqid
    mply1topmat.m
    cA
    cQ
    cR
    vk
    cI
    cJ
    cL
    cN
    cO
    mply1topmat.a
    mply1topmat.q
    mply1topmat.l
    mptcoe1matfsupp
    mptscmfsupp0
end
