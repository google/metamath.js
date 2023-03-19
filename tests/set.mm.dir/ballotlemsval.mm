include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cmin.mm"
include "cif.mm"
include "cmpt.mm"
include "cdif.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "simpl.mm"
include "fveq2d.mm"
include "breq2d.mm"
include "oveq1d.mm"
include "ifbieq1d.mm"
include "mpteq2dva.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "ovex.mm"
include "mptex.mm"
include "fvmpt.mm"

theorem ballotlemsval
  let vx: setvar x
  let cC: class C
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
  disjoint M j
  disjoint N j
  disjoint O j
  disjoint F j
  disjoint c d
  disjoint d k
  assert |- ( C e. ( O \ E ) -> ( S ` C ) = ( i e. ( 1 ... ( M + N ) ) |-> if ( i <_ ( I ` C ) , ( ( ( I ` C ) + 1 ) - i ) , i ) ) )

  proof
    vd
    cC
    vi
    c1
    cM
    cN
    caddc
    co
    #
    cfz
    co
    #
    vi
    cv
    #
    vd
    cv
    #
    cI
    cfv
    #
    cle
    wbr
    #
    @4
    c1
    caddc
    co
    #
    @2
    cmin
    co
    #
    @2
    cif
    #
    cmpt
    #
    vi
    @1
    @2
    cC
    cI
    cfv
    #
    cle
    wbr
    #
    @10
    c1
    caddc
    co
    #
    @2
    cmin
    co
    #
    @2
    cif
    #
    cmpt
    cO
    cE
    cdif
    #
    cS
    @3
    cC
    wceq
    #
    vi
    @1
    @8
    @14
    @16
    @2
    @1
    wcel
    #
    wa
    #
    @5
    @11
    @7
    @13
    @2
    @18
    @4
    @10
    @2
    cle
    @18
    @3
    cC
    cI
    @16
    @17
    simpl
    fveq2d
    #
    breq2d
    @18
    @6
    @12
    @2
    cmin
    @18
    @4
    @10
    c1
    caddc
    @19
    oveq1d
    oveq1d
    ifbieq1d
    mpteq2dva
    cS
    vc
    @15
    vi
    @1
    @2
    vc
    cv
    #
    cI
    cfv
    #
    cle
    wbr
    #
    @21
    c1
    caddc
    co
    #
    @2
    cmin
    co
    #
    @2
    cif
    #
    cmpt
    #
    cmpt
    vd
    @15
    @9
    cmpt
    ballotth.s
    vc
    vd
    @15
    @26
    @9
    @20
    @3
    wceq
    #
    vi
    @1
    @25
    @8
    @27
    @17
    wa
    #
    @22
    @5
    @24
    @7
    @2
    @28
    @21
    @4
    @2
    cle
    @28
    @20
    @3
    cI
    @27
    @17
    simpl
    fveq2d
    #
    breq2d
    @28
    @23
    @6
    @2
    cmin
    @28
    @21
    @4
    c1
    caddc
    @29
    oveq1d
    oveq1d
    ifbieq1d
    mpteq2dva
    cbvmptv
    eqtri
    vi
    @1
    @14
    c1
    @0
    cfz
    ovex
    mptex
    fvmpt
end
