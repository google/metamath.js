include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "wral.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "breq2d.mm"
include "ralbidv.mm"
include "crab.mm"
include "cbvrabv.mm"
include "eqtri.mm"
include "elrab2.mm"

theorem ballotleme
  let vx: setvar x
  let cC: class C
  let cP: class P
  let vi: setvar i
  let cE: class E
  let cF: class F
  let cM: class M
  let cN: class N
  let cO: class O
  let vc: setvar c
  let vd: setvar d
  let vj: setvar j
  let vk: setvar k
  assume ballotth.m: |- M e. NN
  assume ballotth.n: |- N e. NN
  assume ballotth.o: |- O = { c e. ~P ( 1 ... ( M + N ) ) | ( # ` c ) = M }
  assume ballotth.p: |- P = ( x e. ~P O |-> ( ( # ` x ) / ( # ` O ) ) )
  assume ballotth.f: |- F = ( c e. O |-> ( i e. ZZ |-> ( ( # ` ( ( 1 ... i ) i^i c ) ) - ( # ` ( ( 1 ... i ) \ c ) ) ) ) )
  assume ballotth.e: |- E = { c e. O | A. i e. ( 1 ... ( M + N ) ) 0 < ( ( F ` c ) ` i ) }

  disjoint M c
  disjoint N c
  disjoint O c
  disjoint M i
  disjoint N i
  disjoint O i
  disjoint c i
  disjoint F c
  disjoint F i
  disjoint C i
  disjoint c d
  disjoint d i
  disjoint C d
  disjoint F d
  disjoint M d
  disjoint N d
  disjoint O d
  disjoint M j
  disjoint N j
  disjoint O j
  disjoint M k
  disjoint N k
  disjoint O k
  disjoint F j
  disjoint F k
  assert |- ( C e. E <-> ( C e. O /\ A. i e. ( 1 ... ( M + N ) ) 0 < ( ( F ` C ) ` i ) ) )

  proof
    cc0
    vi
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
    clt
    wbr
    #
    vi
    c1
    cM
    cN
    caddc
    co
    cfz
    co
    #
    wral
    #
    cc0
    @0
    cC
    cF
    cfv
    #
    cfv
    #
    clt
    wbr
    #
    vi
    @5
    wral
    vd
    cC
    cO
    cE
    @1
    cC
    wceq
    #
    @4
    @9
    vi
    @5
    @10
    @3
    @8
    cc0
    clt
    @10
    @0
    @2
    @7
    @1
    cC
    cF
    fveq2
    fveq1d
    breq2d
    ralbidv
    cE
    cc0
    @0
    vc
    cv
    #
    cF
    cfv
    #
    cfv
    #
    clt
    wbr
    #
    vi
    @5
    wral
    #
    vc
    cO
    crab
    @6
    vd
    cO
    crab
    ballotth.e
    @15
    @6
    vc
    vd
    cO
    @11
    @1
    wceq
    #
    @14
    @4
    vi
    @5
    @16
    @13
    @3
    cc0
    clt
    @16
    @0
    @12
    @2
    @11
    @1
    cF
    fveq2
    fveq1d
    breq2d
    ralbidv
    cbvrabv
    eqtri
    elrab2
end
