include "wcel.mm"
include "cvv.mm"
include "cima.mm"
include "cimage.mm"
include "cfv.mm"
include "wceq.mm"
include "elex.mm"
include "cv.mm"
include "imaeq2.mm"
include "imageval.mm"
include "fvmptg.mm"
include "sylan.mm"

theorem fvimage
  let cA: class A
  let cR: class R
  let cV: class V
  let cW: class W
  let vx: setvar x


  assert |- ( ( A e. V /\ ( R " A ) e. W ) -> ( Image R ` A ) = ( R " A ) )

  proof
    cA
    cV
    wcel
    cA
    cvv
    wcel
    cR
    cA
    cima
    #
    cW
    wcel
    cA
    cR
    cimage
    #
    cfv
    @0
    wceq
    cA
    cV
    elex
    vx
    cA
    cR
    vx
    cv
    #
    cima
    @0
    cvv
    cW
    @1
    @2
    cA
    cR
    imaeq2
    vx
    cR
    imageval
    fvmptg
    sylan
end
