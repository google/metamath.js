include "wf1.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "dff13.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfeq.mm"
include "nfv.mm"
include "nfim.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "equequ2.mm"
include "imbi12d.mm"
include "cbvral.mm"
include "ralbii.mm"
include "nfral.mm"
include "eqeq1d.mm"
include "equequ1.mm"
include "ralbidv.mm"
include "bitri.mm"
include "anbi2i.mm"

theorem dff13f
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let vw: setvar w
  let vv: setvar v
  assume dff13f.1: |- F/_ x F
  assume dff13f.2: |- F/_ y F

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint w x
  disjoint v x
  disjoint w y
  disjoint v y
  disjoint v w
  disjoint A w
  disjoint A v
  disjoint B w
  disjoint B v
  disjoint F w
  disjoint F v
  assert |- ( F : A -1-1-> B <-> ( F : A --> B /\ A. x e. A A. y e. A ( ( F ` x ) = ( F ` y ) -> x = y ) ) )

  proof
    cA
    cB
    cF
    wf1
    cA
    cB
    cF
    wf
    #
    vw
    cv
    #
    cF
    cfv
    #
    vv
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vw
    vv
    weq
    #
    wi
    #
    vv
    cA
    wral
    #
    vw
    cA
    wral
    #
    wa
    @0
    vx
    cv
    #
    cF
    cfv
    #
    vy
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vx
    vy
    weq
    #
    wi
    #
    vy
    cA
    wral
    #
    vx
    cA
    wral
    #
    wa
    vw
    vv
    cA
    cB
    cF
    dff13
    @9
    @18
    @0
    @9
    @2
    @13
    wceq
    #
    vw
    vy
    weq
    #
    wi
    #
    vy
    cA
    wral
    #
    vw
    cA
    wral
    @18
    @8
    @22
    vw
    cA
    @7
    @21
    vv
    vy
    cA
    @5
    @6
    vy
    vy
    @2
    @4
    vy
    @1
    cF
    dff13f.2
    vy
    @1
    nfcv
    nffv
    vy
    @3
    cF
    dff13f.2
    vy
    @3
    nfcv
    nffv
    nfeq
    @6
    vy
    nfv
    nfim
    @21
    vv
    nfv
    vv
    vy
    weq
    #
    @5
    @19
    @6
    @20
    @23
    @4
    @13
    @2
    @3
    @12
    cF
    fveq2
    eqeq2d
    vv
    vy
    vw
    equequ2
    imbi12d
    cbvral
    ralbii
    @22
    @17
    vw
    vx
    cA
    @21
    vx
    vy
    cA
    vx
    cA
    nfcv
    @19
    @20
    vx
    vx
    @2
    @13
    vx
    @1
    cF
    dff13f.1
    vx
    @1
    nfcv
    nffv
    vx
    @12
    cF
    dff13f.1
    vx
    @12
    nfcv
    nffv
    nfeq
    @20
    vx
    nfv
    nfim
    nfral
    @17
    vw
    nfv
    vw
    vx
    weq
    #
    @21
    @16
    vy
    cA
    @24
    @19
    @14
    @20
    @15
    @24
    @2
    @11
    @13
    @1
    @10
    cF
    fveq2
    eqeq1d
    vw
    vx
    vy
    equequ1
    imbi12d
    ralbidv
    cbvral
    bitri
    anbi2i
    bitri
end
