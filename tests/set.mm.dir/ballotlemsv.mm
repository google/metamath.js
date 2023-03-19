include "cdif.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cmin.mm"
include "cif.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "ballotlemsval.mm"
include "breq1.mm"
include "oveq2.mm"
include "id.mm"
include "ifbieq12d.mm"
include "cbvmptv.mm"
include "syl6eq.mm"
include "adantr.mm"
include "simpr.mm"
include "breq1d.mm"
include "oveq2d.mm"
include "adantlr.mm"
include "ovexd.mm"
include "wn.mm"
include "elex.mm"
include "ad2antlr.mm"
include "ifclda.mm"
include "fvmptd.mm"

theorem ballotlemsv
  let vx: setvar x
  let cC: class C
  let cP: class P
  let cS: class S
  let vi: setvar i
  let vk: setvar k
  let cE: class E
  let cF: class F
  let cI: class I
  let cJ: class J
  let cM: class M
  let cN: class N
  let cO: class O
  let vc: setvar c
  let vd: setvar d
  let vj: setvar j
  assume ballotth.m: |- M e. NN
  assume ballotth.n: |- N e. NN
  assume ballotth.o: |- O = { c e. ~P ( 1 ... ( M + N ) ) | ( # ` c ) = M }
  assume ballotth.p: |- P = ( x e. ~P O |-> ( ( # ` x ) / ( # ` O ) ) )
  assume ballotth.f: |- F = ( c e. O |-> ( i e. ZZ |-> ( ( # ` ( ( 1 ... i ) i^i c ) ) - ( # ` ( ( 1 ... i ) \ c ) ) ) ) )
  assume ballotth.e: |- E = { c e. O | A. i e. ( 1 ... ( M + N ) ) 0 < ( ( F ` c ) ` i ) }
  assume ballotth.mgtn: |- N < M
  assume ballotth.i: |- I = ( c e. ( O \ E ) |-> inf ( { k e. ( 1 ... ( M + N ) ) | ( ( F ` c ) ` k ) = 0 } , RR , < ) )
  assume ballotth.s: |- S = ( c e. ( O \ E ) |-> ( i e. ( 1 ... ( M + N ) ) |-> if ( i <_ ( I ` c ) , ( ( ( I ` c ) + 1 ) - i ) , i ) ) )

  disjoint c i
  disjoint c k
  disjoint M c
  disjoint i k
  disjoint M i
  disjoint M k
  disjoint N c
  disjoint N i
  disjoint N k
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
  disjoint c d
  disjoint d i
  disjoint d k
  disjoint M d
  disjoint N d
  disjoint E d
  disjoint C d
  disjoint I d
  disjoint O d
  disjoint i j
  disjoint I j
  disjoint C j
  disjoint E j
  disjoint F j
  disjoint J j
  disjoint M j
  disjoint N j
  disjoint O j
  disjoint M j
  disjoint N j
  disjoint O j
  disjoint F j
  disjoint c d
  disjoint d k
  assert |- ( ( C e. ( O \ E ) /\ J e. ( 1 ... ( M + N ) ) ) -> ( ( S ` C ) ` J ) = if ( J <_ ( I ` C ) , ( ( ( I ` C ) + 1 ) - J ) , J ) )

  proof
    cC
    cO
    cE
    cdif
    wcel
    #
    cJ
    c1
    cM
    cN
    caddc
    co
    cfz
    co
    #
    wcel
    #
    wa
    #
    vj
    cJ
    vj
    cv
    #
    cC
    cI
    cfv
    #
    cle
    wbr
    #
    @5
    c1
    caddc
    co
    #
    @4
    cmin
    co
    #
    @4
    cif
    #
    cJ
    @5
    cle
    wbr
    #
    @7
    cJ
    cmin
    co
    #
    cJ
    cif
    #
    @1
    cC
    cS
    cfv
    #
    cvv
    @0
    @13
    vj
    @1
    @9
    cmpt
    #
    wceq
    @2
    @0
    @13
    vi
    @1
    vi
    cv
    #
    @5
    cle
    wbr
    #
    @7
    @15
    cmin
    co
    #
    @15
    cif
    #
    cmpt
    @14
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
    vi
    vj
    @1
    @18
    @9
    @15
    @4
    wceq
    #
    @16
    @6
    @17
    @15
    @8
    @4
    @15
    @4
    @5
    cle
    breq1
    @15
    @4
    @7
    cmin
    oveq2
    @19
    id
    ifbieq12d
    cbvmptv
    syl6eq
    adantr
    @0
    @4
    cJ
    wceq
    #
    @9
    @12
    wceq
    @2
    @0
    @20
    wa
    #
    @6
    @10
    @8
    @4
    @11
    cJ
    @21
    @4
    cJ
    @5
    cle
    @0
    @20
    simpr
    #
    breq1d
    @21
    @4
    cJ
    @7
    cmin
    @22
    oveq2d
    @22
    ifbieq12d
    adantlr
    @0
    @2
    simpr
    @3
    @10
    @11
    cJ
    cvv
    @3
    @10
    wa
    @7
    cJ
    cmin
    ovexd
    @2
    cJ
    cvv
    wcel
    @0
    @10
    wn
    cJ
    @1
    elex
    ad2antlr
    ifclda
    fvmptd
end
