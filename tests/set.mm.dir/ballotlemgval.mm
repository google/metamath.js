include "cfn.mm"
include "cv.mm"
include "cin.mm"
include "chash.mm"
include "cfv.mm"
include "cdif.mm"
include "cmin.mm"
include "co.mm"
include "wceq.mm"
include "ineq2.mm"
include "fveq2d.mm"
include "difeq2.mm"
include "oveq12d.mm"
include "ineq1.mm"
include "difeq1.mm"
include "ovex.mm"
include "ovmpt2.mm"

theorem ballotlemgval
  let vx: setvar x
  let vv: setvar v
  let vu: setvar u
  let cP: class P
  let cR: class R
  let cS: class S
  let cU: class U
  let vi: setvar i
  let vk: setvar k
  let cE: class E
  let c.ex: class .^
  let cF: class F
  let cI: class I
  let cM: class M
  let cN: class N
  let cO: class O
  let cV: class V
  let vc: setvar c
  let cC: class C
  let cJ: class J
  let vj: setvar j
  let vd: setvar d
  let cD: class D
  assume ballotth.m: |- M e. NN
  assume ballotth.n: |- N e. NN
  assume ballotth.o: |- O = { c e. ~P ( 1 ... ( M + N ) ) | ( # ` c ) = M }
  assume ballotth.p: |- P = ( x e. ~P O |-> ( ( # ` x ) / ( # ` O ) ) )
  assume ballotth.f: |- F = ( c e. O |-> ( i e. ZZ |-> ( ( # ` ( ( 1 ... i ) i^i c ) ) - ( # ` ( ( 1 ... i ) \ c ) ) ) ) )
  assume ballotth.e: |- E = { c e. O | A. i e. ( 1 ... ( M + N ) ) 0 < ( ( F ` c ) ` i ) }
  assume ballotth.mgtn: |- N < M
  assume ballotth.i: |- I = ( c e. ( O \ E ) |-> inf ( { k e. ( 1 ... ( M + N ) ) | ( ( F ` c ) ` k ) = 0 } , RR , < ) )
  assume ballotth.s: |- S = ( c e. ( O \ E ) |-> ( i e. ( 1 ... ( M + N ) ) |-> if ( i <_ ( I ` c ) , ( ( ( I ` c ) + 1 ) - i ) , i ) ) )
  assume ballotth.r: |- R = ( c e. ( O \ E ) |-> ( ( S ` c ) " c ) )
  assume ballotlemg: |- .^ = ( u e. Fin , v e. Fin |-> ( ( # ` ( v i^i u ) ) - ( # ` ( v \ u ) ) ) )

  disjoint u v
  disjoint I u
  disjoint I v
  disjoint R u
  disjoint R v
  disjoint S u
  disjoint S v
  disjoint U u
  disjoint U v
  disjoint V u
  disjoint V v
  disjoint M c
  disjoint N c
  disjoint O c
  disjoint M i
  disjoint N i
  disjoint O i
  disjoint M k
  disjoint N k
  disjoint O k
  disjoint c i
  disjoint F c
  disjoint F i
  disjoint F k
  disjoint i k
  disjoint E i
  disjoint E k
  disjoint I k
  disjoint c k
  disjoint E c
  disjoint I i
  disjoint I c
  disjoint S k
  disjoint S i
  disjoint S c
  disjoint R i
  disjoint C u
  disjoint C v
  disjoint J u
  disjoint J v
  disjoint M j
  disjoint N j
  disjoint O j
  disjoint F j
  disjoint C i
  disjoint C k
  disjoint c d
  disjoint d k
  disjoint i j
  disjoint I j
  disjoint C j
  disjoint E j
  disjoint J j
  disjoint j k
  disjoint S j
  disjoint J k
  disjoint D i
  disjoint D k
  assert |- ( ( U e. Fin /\ V e. Fin ) -> ( U .^ V ) = ( ( # ` ( V i^i U ) ) - ( # ` ( V \ U ) ) ) )

  proof
    vu
    vv
    cU
    cV
    cfn
    cfn
    vv
    cv
    #
    vu
    cv
    #
    cin
    #
    chash
    cfv
    #
    @0
    @1
    cdif
    #
    chash
    cfv
    #
    cmin
    co
    cV
    cU
    cin
    #
    chash
    cfv
    #
    cV
    cU
    cdif
    #
    chash
    cfv
    #
    cmin
    co
    c.ex
    @0
    cU
    cin
    #
    chash
    cfv
    #
    @0
    cU
    cdif
    #
    chash
    cfv
    #
    cmin
    co
    @1
    cU
    wceq
    #
    @3
    @11
    @5
    @13
    cmin
    @14
    @2
    @10
    chash
    @1
    cU
    @0
    ineq2
    fveq2d
    @14
    @4
    @12
    chash
    @1
    cU
    @0
    difeq2
    fveq2d
    oveq12d
    @0
    cV
    wceq
    #
    @11
    @7
    @13
    @9
    cmin
    @15
    @10
    @6
    chash
    @0
    cV
    cU
    ineq1
    fveq2d
    @15
    @12
    @8
    chash
    @0
    cV
    cU
    difeq1
    fveq2d
    oveq12d
    ballotlemg
    @7
    @9
    cmin
    ovex
    ovmpt2
end
