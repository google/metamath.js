include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wcel.mm"
include "crnk.mm"
include "cfv.mm"
include "cv.mm"
include "csuc.mm"
include "crab.mm"
include "cint.mm"
include "wceq.mm"
include "cvv.mm"
include "unir1.mm"
include "eleqtrri.mm"
include "rankvalb.mm"
include "ax-mp.mm"

theorem rankval
  let vx: setvar x
  let cA: class A
  assume rankval.1: |- A e. _V

  disjoint A x
  assert |- ( rank ` A ) = |^| { x e. On | A e. ( R1 ` suc x ) }

  proof
    cA
    cr1
    con0
    cima
    cuni
    #
    wcel
    cA
    crnk
    cfv
    cA
    vx
    cv
    csuc
    cr1
    cfv
    wcel
    vx
    con0
    crab
    cint
    wceq
    cA
    cvv
    @0
    rankval.1
    unir1
    eleqtrri
    vx
    cA
    rankvalb
    ax-mp
end
