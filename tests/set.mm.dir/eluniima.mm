include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wrex.mm"
include "ciun.mm"
include "wfun.mm"
include "cima.mm"
include "cuni.mm"
include "eliun.mm"
include "funiunfv.mm"
include "eleq2d.mm"
include "syl5rbbr.mm"

theorem eluniima
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F

  disjoint A x
  disjoint B x
  disjoint F x
  assert |- ( Fun F -> ( B e. U. ( F " A ) <-> E. x e. A B e. ( F ` x ) ) )

  proof
    cB
    vx
    cv
    cF
    cfv
    #
    wcel
    vx
    cA
    wrex
    cB
    vx
    cA
    @0
    ciun
    #
    wcel
    cF
    wfun
    #
    cB
    cF
    cA
    cima
    cuni
    #
    wcel
    vx
    cB
    cA
    @0
    eliun
    @2
    @1
    @3
    cB
    vx
    cA
    cF
    funiunfv
    eleq2d
    syl5rbbr
end
