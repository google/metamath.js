include "cv.mm"
include "crnk.mm"
include "cfv.mm"
include "wss.mm"
include "wral.mm"
include "crab.mm"
include "cvv.mm"
include "nfcv.mm"
include "nfv.mm"
include "wceq.mm"
include "fveq2.mm"
include "sseq2d.mm"
include "cbvralf.mm"
include "rabbii.mm"
include "nfral.mm"
include "sseq1d.mm"
include "ralbidv.mm"
include "cbvrab.mm"
include "eqtr4i.mm"
include "scottex.mm"
include "eqeltri.mm"

theorem scottexf
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  let vw: setvar w
  assume scottexf.1: |- F/_ y A
  assume scottexf.2: |- F/_ x A

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w z
  disjoint A z
  disjoint A w
  assert |- { x e. A | A. y e. A ( rank ` x ) C_ ( rank ` y ) } e. _V

  proof
    vx
    cv
    #
    crnk
    cfv
    #
    vy
    cv
    #
    crnk
    cfv
    #
    wss
    #
    vy
    cA
    wral
    #
    vx
    cA
    crab
    #
    vw
    cv
    #
    crnk
    cfv
    #
    vz
    cv
    #
    crnk
    cfv
    #
    wss
    #
    vz
    cA
    wral
    #
    vw
    cA
    crab
    #
    cvv
    @6
    @1
    @10
    wss
    #
    vz
    cA
    wral
    #
    vx
    cA
    crab
    @13
    @5
    @15
    vx
    cA
    @4
    @14
    vy
    vz
    cA
    scottexf.1
    vz
    cA
    nfcv
    @4
    vz
    nfv
    @14
    vy
    nfv
    @2
    @9
    wceq
    @3
    @10
    @1
    @2
    @9
    crnk
    fveq2
    sseq2d
    cbvralf
    rabbii
    @12
    @15
    vw
    vx
    cA
    vw
    cA
    nfcv
    scottexf.2
    @11
    vx
    vz
    cA
    scottexf.2
    @11
    vx
    nfv
    nfral
    @15
    vw
    nfv
    @7
    @0
    wceq
    #
    @11
    @14
    vz
    cA
    @16
    @8
    @1
    @10
    @7
    @0
    crnk
    fveq2
    sseq1d
    ralbidv
    cbvrab
    eqtr4i
    vw
    vz
    cA
    scottex
    eqeltri
end
