include "cv.mm"
include "cr1.mm"
include "cfv.mm"
include "wcel.mm"
include "con0.mm"
include "wrex.mm"
include "wceq.mm"
include "eleq1.mm"
include "rexbidv.mm"
include "vex.mm"
include "tz9.13.mm"
include "vtoclg.mm"

theorem tz9.13g
  let vx: setvar x
  let cA: class A
  let cV: class V
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- ( A e. V -> E. x e. On A e. ( R1 ` x ) )

  proof
    vy
    cv
    #
    vx
    cv
    cr1
    cfv
    #
    wcel
    #
    vx
    con0
    wrex
    cA
    @1
    wcel
    #
    vx
    con0
    wrex
    vy
    cA
    cV
    @0
    cA
    wceq
    @2
    @3
    vx
    con0
    @0
    cA
    @1
    eleq1
    rexbidv
    vx
    @0
    vy
    vex
    tz9.13
    vtoclg
end
