include "cvv.mm"
include "wcel.mm"
include "cdm.mm"
include "cv.mm"
include "cop.mm"
include "wex.mm"
include "wb.mm"
include "eldm2g.mm"
include "ax-mp.mm"

theorem eldm2
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume eldm.1: |- A e. _V

  disjoint A y
  disjoint B y
  assert |- ( A e. dom B <-> E. y <. A , y >. e. B )

  proof
    cA
    cvv
    wcel
    cA
    cB
    cdm
    wcel
    cA
    vy
    cv
    cop
    cB
    wcel
    vy
    wex
    wb
    eldm.1
    vy
    cA
    cB
    cvv
    eldm2g
    ax-mp
end
