include "cvv.mm"
include "wcel.mm"
include "cdom.mm"
include "wbr.mm"
include "cv.mm"
include "wf1.mm"
include "wex.mm"
include "wb.mm"
include "brdomg.mm"
include "ax-mp.mm"

theorem brdom
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vx: setvar x
  assume bren.1: |- B e. _V

  disjoint A f
  disjoint B f
  disjoint f x
  disjoint A x
  disjoint B x
  assert |- ( A ~<_ B <-> E. f f : A -1-1-> B )

  proof
    cB
    cvv
    wcel
    cA
    cB
    cdom
    wbr
    cA
    cB
    vf
    cv
    wf1
    vf
    wex
    wb
    bren.1
    cA
    cB
    cvv
    vf
    brdomg
    ax-mp
end
