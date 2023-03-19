include "wrel.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wex.mm"
include "cuni.mm"
include "elrel.mm"
include "simpr.mm"
include "wi.mm"
include "vex.mm"
include "uniopel.mm"
include "a1i.mm"
include "eleq1.mm"
include "unieq.mm"
include "eleq1d.mm"
include "3imtr4d.mm"
include "exlimivv.mm"
include "sylc.mm"

theorem unielrel
  let cA: class A
  let cR: class R
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( Rel R /\ A e. R ) -> U. A e. U. R )

  proof
    cR
    wrel
    #
    cA
    cR
    wcel
    #
    wa
    cA
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    wceq
    #
    vy
    wex
    vx
    wex
    @1
    cA
    cuni
    #
    cR
    cuni
    #
    wcel
    #
    vx
    vy
    cA
    cR
    elrel
    @0
    @1
    simpr
    @5
    @1
    @8
    wi
    vx
    vy
    @5
    @4
    cR
    wcel
    #
    @4
    cuni
    #
    @7
    wcel
    #
    @1
    @8
    @9
    @11
    wi
    @5
    @2
    @3
    cR
    vx
    vex
    vy
    vex
    uniopel
    a1i
    cA
    @4
    cR
    eleq1
    @5
    @6
    @10
    @7
    cA
    @4
    unieq
    eleq1d
    3imtr4d
    exlimivv
    sylc
end
