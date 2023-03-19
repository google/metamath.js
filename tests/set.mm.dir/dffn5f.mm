include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "wceq.mm"
include "dffn5.mm"
include "nfcv.mm"
include "nffv.mm"
include "fveq2.mm"
include "cbvmpt.mm"
include "eqeq2i.mm"
include "bitri.mm"

theorem dffn5f
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vz: setvar z
  assume dffn5f.1: |- F/_ x F

  disjoint A x
  disjoint x z
  disjoint A z
  disjoint F z
  assert |- ( F Fn A <-> F = ( x e. A |-> ( F ` x ) ) )

  proof
    cF
    cA
    wfn
    cF
    vz
    cA
    vz
    cv
    #
    cF
    cfv
    #
    cmpt
    #
    wceq
    cF
    vx
    cA
    vx
    cv
    #
    cF
    cfv
    #
    cmpt
    #
    wceq
    vz
    cA
    cF
    dffn5
    @2
    @5
    cF
    vz
    vx
    cA
    @1
    @4
    vx
    @0
    cF
    dffn5f.1
    vx
    @0
    nfcv
    nffv
    vz
    @4
    nfcv
    @0
    @3
    cF
    fveq2
    cbvmpt
    eqeq2i
    bitri
end
