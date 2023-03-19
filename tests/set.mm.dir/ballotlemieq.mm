include "cdif.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cmin.mm"
include "cif.mm"
include "cmpt.mm"
include "wa.mm"
include "simpl.mm"
include "breq2d.mm"
include "oveq1d.mm"
include "ifbieq1d.mm"
include "mpteq2dva.mm"
include "3ad2ant3.mm"
include "ballotlemsval.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "3eqtr4d.mm"

theorem ballotlemieq
  let vx: setvar x
  let cC: class C
  let cD: class D
  let cP: class P
  let cS: class S
  let vi: setvar i
  let vk: setvar k
  let cE: class E
  let cF: class F
  let cI: class I
  let cM: class M
  let cN: class N
  let cO: class O
  let vc: setvar c
  let vj: setvar j
  let vd: setvar d
  let cJ: class J
  assume ballotth.m: |- M e. NN
  assume ballotth.n: |- N e. NN
  assume ballotth.o: |- O = { c e. ~P ( 1 ... ( M + N ) ) | ( # ` c ) = M }
  assume ballotth.p: |- P = ( x e. ~P O |-> ( ( # ` x ) / ( # ` O ) ) )
  assume ballotth.f: |- F = ( c e. O |-> ( i e. ZZ |-> ( ( # ` ( ( 1 ... i ) i^i c ) ) - ( # ` ( ( 1 ... i ) \ c ) ) ) ) )
  assume ballotth.e: |- E = { c e. O | A. i e. ( 1 ... ( M + N ) ) 0 < ( ( F ` c ) ` i ) }
  assume ballotth.mgtn: |- N < M
  assume ballotth.i: |- I = ( c e. ( O \ E ) |-> inf ( { k e. ( 1 ... ( M + N ) ) | ( ( F ` c ) ` k ) = 0 } , RR , < ) )
  assume ballotth.s: |- S = ( c e. ( O \ E ) |-> ( i e. ( 1 ... ( M + N ) ) |-> if ( i <_ ( I ` c ) , ( ( ( I ` c ) + 1 ) - i ) , i ) ) )

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
  disjoint C i
  disjoint i k
  disjoint E i
  disjoint E k
  disjoint C k
  disjoint I k
  disjoint c k
  disjoint E c
  disjoint I i
  disjoint I c
  disjoint S k
  disjoint D i
  disjoint D k
  disjoint M j
  disjoint N j
  disjoint O j
  disjoint F j
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
  assert |- ( ( C e. ( O \ E ) /\ D e. ( O \ E ) /\ ( I ` C ) = ( I ` D ) ) -> ( S ` C ) = ( S ` D ) )

  proof
    cC
    cO
    cE
    cdif
    #
    wcel
    #
    cD
    @0
    wcel
    #
    cC
    cI
    cfv
    #
    cD
    cI
    cfv
    #
    wceq
    #
    w3a
    vi
    c1
    cM
    cN
    caddc
    co
    cfz
    co
    #
    vi
    cv
    #
    @3
    cle
    wbr
    #
    @3
    c1
    caddc
    co
    #
    @7
    cmin
    co
    #
    @7
    cif
    #
    cmpt
    #
    vi
    @6
    @7
    @4
    cle
    wbr
    #
    @4
    c1
    caddc
    co
    #
    @7
    cmin
    co
    #
    @7
    cif
    #
    cmpt
    #
    cC
    cS
    cfv
    #
    cD
    cS
    cfv
    #
    @5
    @1
    @12
    @17
    wceq
    @2
    @5
    vi
    @6
    @11
    @16
    @5
    @7
    @6
    wcel
    #
    wa
    #
    @8
    @13
    @10
    @15
    @7
    @21
    @3
    @4
    @7
    cle
    @5
    @20
    simpl
    #
    breq2d
    @21
    @9
    @14
    @7
    cmin
    @21
    @3
    @4
    c1
    caddc
    @22
    oveq1d
    oveq1d
    ifbieq1d
    mpteq2dva
    3ad2ant3
    @1
    @2
    @18
    @12
    wceq
    @5
    vx
    cC
    cP
    cS
    vi
    vk
    cE
    cF
    cI
    cM
    cN
    cO
    vc
    ballotth.m
    ballotth.n
    ballotth.o
    ballotth.p
    ballotth.f
    ballotth.e
    ballotth.mgtn
    ballotth.i
    ballotth.s
    ballotlemsval
    3ad2ant1
    @2
    @1
    @19
    @17
    wceq
    @5
    vx
    cD
    cP
    cS
    vi
    vk
    cE
    cF
    cI
    cM
    cN
    cO
    vc
    ballotth.m
    ballotth.n
    ballotth.o
    ballotth.p
    ballotth.f
    ballotth.e
    ballotth.mgtn
    ballotth.i
    ballotth.s
    ballotlemsval
    3ad2ant2
    3eqtr4d
end
