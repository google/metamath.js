include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "cpw.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "wss.mm"
include "cv.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "crab.mm"
include "cbvrabv.mm"
include "eqtri.mm"
include "elrab2.mm"
include "ovex.mm"
include "elpw2.mm"
include "anbi1i.mm"
include "bitri.mm"

theorem ballotlemelo
  let cC: class C
  let cM: class M
  let cN: class N
  let cO: class O
  let vc: setvar c
  let vd: setvar d
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  assume ballotth.m: |- M e. NN
  assume ballotth.n: |- N e. NN
  assume ballotth.o: |- O = { c e. ~P ( 1 ... ( M + N ) ) | ( # ` c ) = M }

  disjoint M c
  disjoint N c
  disjoint O c
  disjoint c d
  disjoint C d
  disjoint M d
  disjoint N d
  disjoint M i
  disjoint N i
  disjoint O i
  disjoint M j
  disjoint N j
  disjoint O j
  disjoint M k
  disjoint N k
  disjoint O k
  assert |- ( C e. O <-> ( C C_ ( 1 ... ( M + N ) ) /\ ( # ` C ) = M ) )

  proof
    cC
    cO
    wcel
    cC
    c1
    cM
    cN
    caddc
    co
    #
    cfz
    co
    #
    cpw
    #
    wcel
    #
    cC
    chash
    cfv
    #
    cM
    wceq
    #
    wa
    cC
    @1
    wss
    #
    @5
    wa
    vd
    cv
    #
    chash
    cfv
    #
    cM
    wceq
    #
    @5
    vd
    cC
    @2
    cO
    @7
    cC
    wceq
    @8
    @4
    cM
    @7
    cC
    chash
    fveq2
    eqeq1d
    cO
    vc
    cv
    #
    chash
    cfv
    #
    cM
    wceq
    #
    vc
    @2
    crab
    @9
    vd
    @2
    crab
    ballotth.o
    @12
    @9
    vc
    vd
    @2
    @10
    @7
    wceq
    @11
    @8
    cM
    @10
    @7
    chash
    fveq2
    eqeq1d
    cbvrabv
    eqtri
    elrab2
    @3
    @6
    @5
    cC
    @1
    c1
    @0
    cfz
    ovex
    elpw2
    anbi1i
    bitri
end
