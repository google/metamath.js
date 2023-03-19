include "wfun.mm"
include "cv.mm"
include "cfv.mm"
include "ciun.mm"
include "cima.mm"
include "cuni.mm"
include "nfcv.mm"
include "nffv.mm"
include "fveq2.mm"
include "cbviun.mm"
include "funiunfv.mm"
include "syl5eqr.mm"

theorem funiunfvf
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vz: setvar z
  assume funiunfvf.1: |- F/_ x F

  disjoint A x
  disjoint x z
  disjoint A z
  disjoint F z
  assert |- ( Fun F -> U_ x e. A ( F ` x ) = U. ( F " A ) )

  proof
    cF
    wfun
    vx
    cA
    vx
    cv
    #
    cF
    cfv
    #
    ciun
    vz
    cA
    vz
    cv
    #
    cF
    cfv
    #
    ciun
    cF
    cA
    cima
    cuni
    vz
    vx
    cA
    @3
    @1
    vx
    @2
    cF
    funiunfvf.1
    vx
    @2
    nfcv
    nffv
    vz
    @1
    nfcv
    @2
    @0
    cF
    fveq2
    cbviun
    vz
    cA
    cF
    funiunfv
    syl5eqr
end
