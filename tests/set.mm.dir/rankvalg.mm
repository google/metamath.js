include "cv.mm"
include "crnk.mm"
include "cfv.mm"
include "csuc.mm"
include "cr1.mm"
include "wcel.mm"
include "con0.mm"
include "crab.mm"
include "cint.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq1.mm"
include "rabbidv.mm"
include "inteqd.mm"
include "eqeq12d.mm"
include "vex.mm"
include "rankval.mm"
include "vtoclg.mm"

theorem rankvalg
  let vx: setvar x
  let cA: class A
  let cV: class V
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- ( A e. V -> ( rank ` A ) = |^| { x e. On | A e. ( R1 ` suc x ) } )

  proof
    vy
    cv
    #
    crnk
    cfv
    #
    @0
    vx
    cv
    csuc
    cr1
    cfv
    #
    wcel
    #
    vx
    con0
    crab
    #
    cint
    #
    wceq
    cA
    crnk
    cfv
    #
    cA
    @2
    wcel
    #
    vx
    con0
    crab
    #
    cint
    #
    wceq
    vy
    cA
    cV
    @0
    cA
    wceq
    #
    @1
    @6
    @5
    @9
    @0
    cA
    crnk
    fveq2
    @10
    @4
    @8
    @10
    @3
    @7
    vx
    con0
    @0
    cA
    @2
    eleq1
    rabbidv
    inteqd
    eqeq12d
    vx
    @0
    vy
    vex
    rankval
    vtoclg
end
