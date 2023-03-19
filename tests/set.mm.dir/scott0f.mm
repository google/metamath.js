include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "crnk.mm"
include "cfv.mm"
include "wss.mm"
include "wral.mm"
include "crab.mm"
include "scott0.mm"
include "nfcv.mm"
include "nfv.mm"
include "fveq2.mm"
include "sseq2d.mm"
include "cbvralf.mm"
include "rabbii.mm"
include "nfral.mm"
include "sseq1d.mm"
include "ralbidv.mm"
include "cbvrab.mm"
include "eqtr4i.mm"
include "eqeq1i.mm"
include "bitr4i.mm"

theorem scott0f
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  let vw: setvar w
  assume scott0f.1: |- F/_ y A
  assume scott0f.2: |- F/_ x A

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w z
  disjoint A z
  disjoint A w
  assert |- ( A = (/) <-> { x e. A | A. y e. A ( rank ` x ) C_ ( rank ` y ) } = (/) )

  proof
    cA
    c0
    wceq
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
    c0
    wceq
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
    c0
    wceq
    vw
    vz
    cA
    scott0
    @13
    @6
    c0
    @13
    @8
    @3
    wss
    #
    vz
    cA
    wral
    #
    vx
    cA
    crab
    @6
    @12
    @15
    vx
    cA
    @11
    @14
    vy
    vz
    cA
    scott0f.1
    vz
    cA
    nfcv
    @11
    vz
    nfv
    @14
    vy
    nfv
    @9
    @2
    wceq
    @10
    @3
    @8
    @9
    @2
    crnk
    fveq2
    sseq2d
    cbvralf
    rabbii
    @5
    @15
    vw
    vx
    cA
    vw
    cA
    nfcv
    scott0f.2
    @4
    vx
    vz
    cA
    scott0f.2
    @4
    vx
    nfv
    nfral
    @15
    vw
    nfv
    @0
    @7
    wceq
    #
    @4
    @14
    vz
    cA
    @16
    @1
    @8
    @3
    @0
    @7
    crnk
    fveq2
    sseq1d
    ralbidv
    cbvrab
    eqtr4i
    eqeq1i
    bitr4i
end
