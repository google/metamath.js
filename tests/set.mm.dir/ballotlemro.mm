include "cdif.mm"
include "wcel.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "wss.mm"
include "chash.mm"
include "wceq.mm"
include "cima.mm"
include "ballotlemrval.mm"
include "crn.mm"
include "imassrn.mm"
include "wf1o.mm"
include "wfo.mm"
include "ccnv.mm"
include "ballotlemsf1o.mm"
include "simpld.mm"
include "f1ofo.mm"
include "forn.mm"
include "3syl.mm"
include "syl5sseq.mm"
include "eqsstrd.mm"
include "cen.mm"
include "wbr.mm"
include "wf1.mm"
include "f1of1.mm"
include "syl.mm"
include "wa.mm"
include "eldifi.mm"
include "ballotlemelo.mm"
include "sylib.mm"
include "id.mm"
include "f1imaeng.mm"
include "syl3anc.mm"
include "eqbrtrd.mm"
include "hasheni.mm"
include "simprd.mm"
include "eqtrd.mm"
include "sylanbrc.mm"

theorem ballotlemro
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
  assert |- ( C e. ( O \ E ) -> ( R ` C ) e. O )

  proof
    cC
    cO
    cE
    cdif
    #
    wcel
    #
    cC
    cR
    cfv
    #
    c1
    cM
    cN
    caddc
    co
    cfz
    co
    #
    wss
    @2
    chash
    cfv
    #
    cM
    wceq
    @2
    cO
    wcel
    @1
    @2
    cC
    cS
    cfv
    #
    cC
    cima
    #
    @3
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
    #
    @1
    @5
    crn
    #
    @6
    @3
    @5
    cC
    imassrn
    @1
    @3
    @3
    @5
    wf1o
    #
    @3
    @3
    @5
    wfo
    @8
    @3
    wceq
    @1
    @9
    @5
    ccnv
    @5
    wceq
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
    simpld
    #
    @3
    @3
    @5
    f1ofo
    @3
    @3
    @5
    forn
    3syl
    syl5sseq
    eqsstrd
    @1
    @4
    cC
    chash
    cfv
    #
    cM
    @1
    @2
    cC
    cen
    wbr
    @4
    @11
    wceq
    @1
    @2
    @6
    cC
    cen
    @7
    @1
    @3
    @3
    @5
    wf1
    #
    cC
    @3
    wss
    #
    @1
    @6
    cC
    cen
    wbr
    @1
    @9
    @12
    @10
    @3
    @3
    @5
    f1of1
    syl
    @1
    @13
    @11
    cM
    wceq
    #
    @1
    cC
    cO
    wcel
    @13
    @14
    wa
    cC
    cO
    cE
    eldifi
    cC
    cM
    cN
    cO
    vc
    ballotth.m
    ballotth.n
    ballotth.o
    ballotlemelo
    sylib
    #
    simpld
    @1
    id
    @3
    @3
    cC
    @5
    @0
    f1imaeng
    syl3anc
    eqbrtrd
    @2
    cC
    hasheni
    syl
    @1
    @13
    @14
    @15
    simprd
    eqtrd
    @2
    cM
    cN
    cO
    vc
    ballotth.m
    ballotth.n
    ballotth.o
    ballotlemelo
    sylanbrc
end
