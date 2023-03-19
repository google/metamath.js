include "cv.mm"
include "cfv.mm"
include "cima.mm"
include "cdif.mm"
include "wceq.mm"
include "fveq2.mm"
include "id.mm"
include "imaeq12d.mm"
include "cmpt.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "cvv.mm"
include "wcel.mm"
include "fvex.mm"
include "imaexg.mm"
include "ax-mp.mm"
include "fvmpt.mm"

theorem ballotlemrval
  let vx: setvar x
  let cC: class C
  let cP: class P
  let cR: class R
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
  let vd: setvar d
  let vj: setvar j
  let cJ: class J
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

  disjoint c i
  disjoint I c
  disjoint I i
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
  disjoint S i
  disjoint S c
  disjoint E d
  disjoint O d
  disjoint C d
  disjoint S d
  disjoint c d
  disjoint d i
  disjoint I d
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
  disjoint D i
  disjoint D k
  assert |- ( C e. ( O \ E ) -> ( R ` C ) = ( ( S ` C ) " C ) )

  proof
    vd
    cC
    vd
    cv
    #
    cS
    cfv
    #
    @0
    cima
    #
    cC
    cS
    cfv
    #
    cC
    cima
    #
    cO
    cE
    cdif
    #
    cR
    @0
    cC
    wceq
    #
    @1
    @3
    @0
    cC
    @0
    cC
    cS
    fveq2
    @6
    id
    imaeq12d
    cR
    vc
    @5
    vc
    cv
    #
    cS
    cfv
    #
    @7
    cima
    #
    cmpt
    vd
    @5
    @2
    cmpt
    ballotth.r
    vc
    vd
    @5
    @9
    @2
    @7
    @0
    wceq
    #
    @8
    @1
    @7
    @0
    @7
    @0
    cS
    fveq2
    @10
    id
    imaeq12d
    cbvmptv
    eqtri
    @3
    cvv
    wcel
    @4
    cvv
    wcel
    cC
    cS
    fvex
    @3
    cC
    cvv
    imaexg
    ax-mp
    fvmpt
end
