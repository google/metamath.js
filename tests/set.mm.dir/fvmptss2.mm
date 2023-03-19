include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "wss.mm"
include "cvv.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "eleq1d.mm"
include "dmmpt.mm"
include "elrab2.mm"
include "fvmptg.mm"
include "eqimss.mm"
include "syl.mm"
include "sylbi.mm"
include "wn.mm"
include "c0.mm"
include "ndmfv.mm"
include "0ss.mm"
include "syl6eqss.mm"
include "pm2.61i.mm"

theorem fvmptss2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  assume fvmptn.1: |- ( x = D -> B = C )
  assume fvmptn.2: |- F = ( x e. A |-> B )

  disjoint A x
  disjoint C x
  disjoint D x
  assert |- ( F ` D ) C_ C

  proof
    cD
    cF
    cdm
    #
    wcel
    #
    cD
    cF
    cfv
    #
    cC
    wss
    #
    @1
    cD
    cA
    wcel
    cC
    cvv
    wcel
    #
    wa
    #
    @3
    cB
    cvv
    wcel
    @4
    vx
    cD
    cA
    @0
    vx
    cv
    cD
    wceq
    cB
    cC
    cvv
    fvmptn.1
    eleq1d
    vx
    cA
    cB
    cF
    fvmptn.2
    dmmpt
    elrab2
    @5
    @2
    cC
    wceq
    @3
    vx
    cD
    cB
    cC
    cA
    cvv
    cF
    fvmptn.1
    fvmptn.2
    fvmptg
    @2
    cC
    eqimss
    syl
    sylbi
    @1
    wn
    @2
    c0
    cC
    cD
    cF
    ndmfv
    cC
    0ss
    syl6eqss
    pm2.61i
end
