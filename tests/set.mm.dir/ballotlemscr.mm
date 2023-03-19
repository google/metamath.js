include "cdif.mm"
include "wcel.mm"
include "cfv.mm"
include "cima.mm"
include "ccnv.mm"
include "ballotlemrval.mm"
include "imaeq2d.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "wf1o.mm"
include "wceq.mm"
include "ballotlemsf1o.mm"
include "simprd.mm"
include "imaeq1d.mm"
include "wf1.mm"
include "wss.mm"
include "simpld.mm"
include "f1of1.mm"
include "syl.mm"
include "eldifi.mm"
include "chash.mm"
include "ballotlemelo.mm"
include "simplbi.mm"
include "f1imacnv.mm"
include "syl2anc.mm"
include "3eqtr2d.mm"

theorem ballotlemscr
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
  let vj: setvar j
  let vd: setvar d
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
  assert |- ( C e. ( O \ E ) -> ( ( S ` C ) " ( R ` C ) ) = C )

  proof
    cC
    cO
    cE
    cdif
    wcel
    #
    cC
    cS
    cfv
    #
    cC
    cR
    cfv
    #
    cima
    @1
    @1
    cC
    cima
    #
    cima
    @1
    ccnv
    #
    @3
    cima
    #
    cC
    @0
    @2
    @3
    @1
    vx
    cC
    cP
    cR
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
    ballotth.r
    ballotlemrval
    imaeq2d
    @0
    @4
    @1
    @3
    @0
    c1
    cM
    cN
    caddc
    co
    cfz
    co
    #
    @6
    @1
    wf1o
    #
    @4
    @1
    wceq
    #
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
    ballotlemsf1o
    #
    simprd
    imaeq1d
    @0
    @6
    @6
    @1
    wf1
    #
    cC
    @6
    wss
    #
    @5
    cC
    wceq
    @0
    @7
    @10
    @0
    @7
    @8
    @9
    simpld
    @6
    @6
    @1
    f1of1
    syl
    @0
    cC
    cO
    wcel
    #
    @11
    cC
    cO
    cE
    eldifi
    @12
    @11
    cC
    chash
    cfv
    cM
    wceq
    cC
    cM
    cN
    cO
    vc
    ballotth.m
    ballotth.n
    ballotth.o
    ballotlemelo
    simplbi
    syl
    @6
    @6
    cC
    @1
    f1imacnv
    syl2anc
    3eqtr2d
end
