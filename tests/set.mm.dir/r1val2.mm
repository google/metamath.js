include "con0.mm"
include "wcel.mm"
include "cv.mm"
include "crnk.mm"
include "cfv.mm"
include "cr1.mm"
include "vex.mm"
include "rankr1a.mm"
include "abbi2dv.mm"

theorem r1val2
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- ( A e. On -> ( R1 ` A ) = { x | ( rank ` x ) e. A } )

  proof
    cA
    con0
    wcel
    vx
    cv
    #
    crnk
    cfv
    cA
    wcel
    vx
    cA
    cr1
    cfv
    @0
    cA
    vx
    vex
    rankr1a
    abbi2dv
end
