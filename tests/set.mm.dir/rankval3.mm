include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wcel.mm"
include "crnk.mm"
include "cfv.mm"
include "cv.mm"
include "wral.mm"
include "crab.mm"
include "cint.mm"
include "wceq.mm"
include "cvv.mm"
include "unir1.mm"
include "eleqtrri.mm"
include "rankval3b.mm"
include "ax-mp.mm"

theorem rankval3
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume rankval3.1: |- A e. _V

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( rank ` A ) = |^| { x e. On | A. y e. A ( rank ` y ) e. x }

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
    vy
    cv
    crnk
    cfv
    vx
    cv
    wcel
    vy
    cA
    wral
    vx
    con0
    crab
    cint
    wceq
    cA
    cvv
    @0
    rankval3.1
    unir1
    eleqtrri
    vx
    vy
    cA
    rankval3b
    ax-mp
end
