include "cv.mm"
include "cfv.mm"
include "wne.mm"
include "crab.mm"
include "nfcv.mm"
include "nfv.mm"
include "nfcii.mm"
include "nffv.mm"
include "nfne.mm"
include "weq.mm"
include "fveq2.mm"
include "neeq12d.mm"
include "cbvrab.mm"
include "eqtri.mm"

theorem bnj1534
  let vx: setvar x
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cD: class D
  let cF: class F
  let cH: class H
  assume bnj1534.1: |- D = { x e. A | ( F ` x ) =/= ( H ` x ) }
  assume bnj1534.2: |- ( w e. F -> A. x w e. F )

  disjoint A w
  disjoint A x
  disjoint A z
  disjoint w x
  disjoint w z
  disjoint x z
  disjoint F w
  disjoint F z
  disjoint H w
  disjoint H x
  disjoint H z
  assert |- D = { z e. A | ( F ` z ) =/= ( H ` z ) }

  proof
    cD
    vx
    cv
    #
    cF
    cfv
    #
    @0
    cH
    cfv
    #
    wne
    #
    vx
    cA
    crab
    vz
    cv
    #
    cF
    cfv
    #
    @4
    cH
    cfv
    #
    wne
    #
    vz
    cA
    crab
    bnj1534.1
    @3
    @7
    vx
    vz
    cA
    vx
    cA
    nfcv
    vz
    cA
    nfcv
    @3
    vz
    nfv
    vx
    @5
    @6
    vx
    @4
    cF
    vx
    vw
    cF
    bnj1534.2
    nfcii
    vx
    @4
    nfcv
    nffv
    vx
    @6
    nfcv
    nfne
    vx
    vz
    weq
    @1
    @5
    @2
    @6
    @0
    @4
    cF
    fveq2
    @0
    @4
    cH
    fveq2
    neeq12d
    cbvrab
    eqtri
end
