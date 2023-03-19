include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "wb.mm"
include "clel2g.mm"
include "ax-mp.mm"

theorem clel2
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume clel2.1: |- A e. _V

  disjoint A x
  disjoint B x
  assert |- ( A e. B <-> A. x ( x = A -> x e. B ) )

  proof
    cA
    cvv
    wcel
    cA
    cB
    wcel
    vx
    cv
    #
    cA
    wceq
    @0
    cB
    wcel
    wi
    vx
    wal
    wb
    clel2.1
    vx
    cA
    cB
    cvv
    clel2g
    ax-mp
end
