include "wf.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "ffnfv.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfel.mm"
include "nfv.mm"
include "weq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "cbvralf.mm"
include "anbi2i.mm"
include "bitri.mm"

theorem ffnfvf
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let vz: setvar z
  assume ffnfvf.1: |- F/_ x A
  assume ffnfvf.2: |- F/_ x B
  assume ffnfvf.3: |- F/_ x F


  assert |- ( F : A --> B <-> ( F Fn A /\ A. x e. A ( F ` x ) e. B ) )

  proof
    cA
    cB
    cF
    wf
    cF
    cA
    wfn
    #
    vz
    cv
    #
    cF
    cfv
    #
    cB
    wcel
    #
    vz
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
    cB
    wcel
    #
    vx
    cA
    wral
    #
    wa
    vz
    cA
    cB
    cF
    ffnfv
    @4
    @8
    @0
    @3
    @7
    vz
    vx
    cA
    vz
    cA
    nfcv
    ffnfvf.1
    vx
    @2
    cB
    vx
    @1
    cF
    ffnfvf.3
    vx
    @1
    nfcv
    nffv
    ffnfvf.2
    nfel
    @7
    vz
    nfv
    vz
    vx
    weq
    @2
    @6
    cB
    @1
    @5
    cF
    fveq2
    eleq1d
    cbvralf
    anbi2i
    bitri
end
