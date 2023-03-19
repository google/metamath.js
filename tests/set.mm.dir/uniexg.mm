include "cv.mm"
include "cuni.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "unieq.mm"
include "eleq1d.mm"
include "vuniex.mm"
include "vtoclg.mm"

theorem uniexg
  let cA: class A
  let cV: class V
  let vx: setvar x


  assert |- ( A e. V -> U. A e. _V )

  proof
    vx
    cv
    #
    cuni
    #
    cvv
    wcel
    cA
    cuni
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
    unieq
    eleq1d
    vx
    vuniex
    vtoclg
end
