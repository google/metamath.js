include "cv.mm"
include "cuni.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "unieq.mm"
include "eleq1d.mm"
include "uniex2.mm"
include "issetri.mm"
include "vtocl.mm"

theorem uniex
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  assume uniex.1: |- A e. _V


  assert |- U. A e. _V

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
    uniex.1
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
    vy
    @1
    vx
    vy
    uniex2
    issetri
    vtocl
end
