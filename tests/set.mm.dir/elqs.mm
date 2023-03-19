include "cvv.mm"
include "wcel.mm"
include "cqs.mm"
include "cv.mm"
include "cec.mm"
include "wceq.mm"
include "wrex.mm"
include "wb.mm"
include "elqsg.mm"
include "ax-mp.mm"

theorem elqs
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  assume elqs.1: |- B e. _V

  disjoint A x
  disjoint B x
  disjoint R x
  assert |- ( B e. ( A /. R ) <-> E. x e. A B = [ x ] R )

  proof
    cB
    cvv
    wcel
    cB
    cA
    cR
    cqs
    wcel
    cB
    vx
    cv
    cR
    cec
    wceq
    vx
    cA
    wrex
    wb
    elqs.1
    vx
    cA
    cB
    cR
    cvv
    elqsg
    ax-mp
end
