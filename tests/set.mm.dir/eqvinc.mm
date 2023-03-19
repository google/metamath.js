include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "cv.mm"
include "wa.mm"
include "wex.mm"
include "wb.mm"
include "eqvincg.mm"
include "ax-mp.mm"

theorem eqvinc
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume eqvinc.1: |- A e. _V

  disjoint A x
  disjoint B x
  assert |- ( A = B <-> E. x ( x = A /\ x = B ) )

  proof
    cA
    cvv
    wcel
    cA
    cB
    wceq
    vx
    cv
    #
    cA
    wceq
    @0
    cB
    wceq
    wa
    vx
    wex
    wb
    eqvinc.1
    vx
    cA
    cB
    cvv
    eqvincg
    ax-mp
end
