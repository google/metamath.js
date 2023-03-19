include "cvv.mm"
include "wcel.mm"
include "cdm.mm"
include "cv.mm"
include "wbr.mm"
include "wex.mm"
include "wb.mm"
include "eldmg.mm"
include "ax-mp.mm"

theorem eldm
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume eldm.1: |- A e. _V

  disjoint A y
  disjoint B y
  assert |- ( A e. dom B <-> E. y A B y )

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
    cB
    wbr
    vy
    wex
    wb
    eldm.1
    vy
    cA
    cB
    cvv
    eldmg
    ax-mp
end
