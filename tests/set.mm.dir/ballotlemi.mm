include "cv.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "cdif.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "eqeq1d.mm"
include "rabbidv.mm"
include "infeq1d.mm"
include "cmpt.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "ltso.mm"
include "infex.mm"
include "fvmpt.mm"

theorem ballotlemi
  let vx: setvar x
  let cC: class C
  let cP: class P
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
  disjoint C d
  disjoint E d
  disjoint F d
  disjoint M d
  disjoint N d
  disjoint O d
  disjoint M j
  disjoint N j
  disjoint O j
  disjoint F j
  disjoint c d
  disjoint d k
  assert |- ( C e. ( O \ E ) -> ( I ` C ) = inf ( { k e. ( 1 ... ( M + N ) ) | ( ( F ` C ) ` k ) = 0 } , RR , < ) )

  proof
    vd
    cC
    vk
    cv
    #
    vd
    cv
    #
    cF
    cfv
    #
    cfv
    #
    cc0
    wceq
    #
    vk
    c1
    cM
    cN
    caddc
    co
    cfz
    co
    #
    crab
    #
    cr
    clt
    cinf
    #
    @0
    cC
    cF
    cfv
    #
    cfv
    #
    cc0
    wceq
    #
    vk
    @5
    crab
    #
    cr
    clt
    cinf
    cO
    cE
    cdif
    #
    cI
    @1
    cC
    wceq
    #
    cr
    @6
    @11
    clt
    @13
    @4
    @10
    vk
    @5
    @13
    @3
    @9
    cc0
    @13
    @0
    @2
    @8
    @1
    cC
    cF
    fveq2
    fveq1d
    eqeq1d
    rabbidv
    infeq1d
    cI
    vc
    @12
    @0
    vc
    cv
    #
    cF
    cfv
    #
    cfv
    #
    cc0
    wceq
    #
    vk
    @5
    crab
    #
    cr
    clt
    cinf
    #
    cmpt
    vd
    @12
    @7
    cmpt
    ballotth.i
    vc
    vd
    @12
    @19
    @7
    @14
    @1
    wceq
    #
    cr
    @18
    @6
    clt
    @20
    @17
    @4
    vk
    @5
    @20
    @16
    @3
    cc0
    @20
    @0
    @15
    @2
    @14
    @1
    cF
    fveq2
    fveq1d
    eqeq1d
    rabbidv
    infeq1d
    cbvmptv
    eqtri
    cr
    @11
    clt
    ltso
    infex
    fvmpt
end
