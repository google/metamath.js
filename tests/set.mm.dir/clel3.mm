include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "wb.mm"
include "clel3g.mm"
include "ax-mp.mm"

theorem clel3
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume clel3.1: |- B e. _V

  disjoint A x
  disjoint B x
  assert |- ( A e. B <-> E. x ( x = B /\ A e. x ) )

  proof
    cB
    cvv
    wcel
    cA
    cB
    wcel
    vx
    cv
    #
    cB
    wceq
    cA
    @0
    wcel
    wa
    vx
    wex
    wb
    clel3.1
    vx
    cA
    cB
    cvv
    clel3g
    ax-mp
end
