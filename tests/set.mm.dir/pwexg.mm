include "cv.mm"
include "cpw.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "pweq.mm"
include "eleq1d.mm"
include "vpwex.mm"
include "vtoclg.mm"

theorem pwexg
  let cA: class A
  let cV: class V
  let vx: setvar x


  assert |- ( A e. V -> ~P A e. _V )

  proof
    vx
    cv
    #
    cpw
    #
    cvv
    wcel
    cA
    cpw
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
    pweq
    eleq1d
    vx
    vpwex
    vtoclg
end
