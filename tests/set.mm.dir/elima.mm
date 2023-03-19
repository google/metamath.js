include "cvv.mm"
include "wcel.mm"
include "cima.mm"
include "cv.mm"
include "wbr.mm"
include "wrex.mm"
include "wb.mm"
include "elimag.mm"
include "ax-mp.mm"

theorem elima
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume elima.1: |- A e. _V

  disjoint A x
  disjoint B x
  disjoint C x
  assert |- ( A e. ( B " C ) <-> E. x e. C x B A )

  proof
    cA
    cvv
    wcel
    cA
    cB
    cC
    cima
    wcel
    vx
    cv
    cA
    cB
    wbr
    vx
    cC
    wrex
    wb
    elima.1
    vx
    cA
    cB
    cC
    cvv
    elimag
    ax-mp
end
