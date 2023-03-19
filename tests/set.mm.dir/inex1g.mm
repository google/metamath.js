include "cv.mm"
include "cin.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "ineq1.mm"
include "eleq1d.mm"
include "vex.mm"
include "inex1.mm"
include "vtoclg.mm"

theorem inex1g
  let cA: class A
  let cB: class B
  let cV: class V
  let vx: setvar x


  assert |- ( A e. V -> ( A i^i B ) e. _V )

  proof
    vx
    cv
    #
    cB
    cin
    #
    cvv
    wcel
    cA
    cB
    cin
    #
    cvv
    wcel
    vx
    cA
    cV
    @0
    cA
    wceq
    @1
    @2
    cvv
    @0
    cA
    cB
    ineq1
    eleq1d
    @0
    cB
    vx
    vex
    inex1
    vtoclg
end
