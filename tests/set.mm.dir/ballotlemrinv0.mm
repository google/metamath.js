include "cdif.mm"
include "wcel.mm"
include "cfv.mm"
include "cima.mm"
include "wceq.mm"
include "wa.mm"
include "ballotlemrval.mm"
include "adantr.mm"
include "simpr.mm"
include "eqtr4d.mm"
include "ballotlemrc.mm"
include "eqeltrrd.mm"
include "ccnv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "wf1o.mm"
include "ballotlemsf1o.mm"
include "simprd.mm"
include "eqcomd.mm"
include "imaeq12d.mm"
include "simpl.mm"
include "ballotlemirc.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "ballotlemieq.mm"
include "syl3anc.mm"
include "imaeq1d.mm"
include "wf1.mm"
include "wss.mm"
include "simpld.mm"
include "f1of1.mm"
include "3syl.mm"
include "eldifi.mm"
include "chash.mm"
include "ballotlemelo.mm"
include "simplbi.mm"
include "f1imacnv.mm"
include "syl2anc.mm"
include "3eqtr3rd.mm"
include "jca.mm"

theorem ballotlemrinv0
  let vx: setvar x
  let cC: class C
  let cD: class D
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

  disjoint i x
  disjoint i k
  disjoint k x
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
  disjoint S i
  disjoint S c
  disjoint R i
  disjoint R k
  disjoint c x
  disjoint C x
  disjoint F x
  disjoint M x
  disjoint N x
  disjoint d i
  disjoint d x
  disjoint d k
  disjoint E d
  disjoint I d
  disjoint O d
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
  disjoint S d
  assert |- ( ( C e. ( O \ E ) /\ D = ( ( S ` C ) " C ) ) -> ( D e. ( O \ E ) /\ C = ( ( S ` D ) " D ) ) )

  proof
    cC
    cO
    cE
    cdif
    #
    wcel
    #
    cD
    cC
    cS
    cfv
    #
    cC
    cima
    #
    wceq
    #
    wa
    #
    cD
    @0
    wcel
    #
    cC
    cD
    cS
    cfv
    #
    cD
    cima
    #
    wceq
    @5
    cC
    cR
    cfv
    #
    cD
    @0
    @5
    @9
    @3
    cD
    @1
    @9
    @3
    wceq
    @4
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
    adantr
    @1
    @4
    simpr
    #
    eqtr4d
    #
    @1
    @9
    @0
    wcel
    @4
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
    ballotlemrc
    adantr
    eqeltrrd
    #
    @5
    @2
    cD
    cima
    @2
    ccnv
    #
    @3
    cima
    #
    @8
    cC
    @5
    @2
    @13
    cD
    @3
    @5
    @13
    @2
    @1
    @13
    @2
    wceq
    #
    @4
    @1
    c1
    cM
    cN
    caddc
    co
    cfz
    co
    #
    @16
    @2
    wf1o
    #
    @15
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
    adantr
    eqcomd
    @10
    imaeq12d
    @5
    @2
    @7
    cD
    @5
    @1
    @6
    cC
    cI
    cfv
    #
    cD
    cI
    cfv
    #
    wceq
    @2
    @7
    wceq
    @1
    @4
    simpl
    #
    @12
    @5
    @9
    cI
    cfv
    #
    @19
    @20
    @1
    @22
    @19
    wceq
    @4
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
    ballotlemirc
    adantr
    @5
    @9
    cD
    cI
    @11
    fveq2d
    eqtr3d
    vx
    cC
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
    ballotlemieq
    syl3anc
    imaeq1d
    @5
    @16
    @16
    @2
    wf1
    #
    cC
    @16
    wss
    #
    @14
    cC
    wceq
    @5
    @1
    @17
    @23
    @21
    @1
    @17
    @15
    @18
    simpld
    @16
    @16
    @2
    f1of1
    3syl
    @5
    @1
    cC
    cO
    wcel
    #
    @24
    @21
    cC
    cO
    cE
    eldifi
    @25
    @24
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
    3syl
    @16
    @16
    cC
    @2
    f1imacnv
    syl2anc
    3eqtr3rd
    jca
end
