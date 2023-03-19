include "cv.mm"
include "chf.mm"
include "wcel.mm"
include "crnk.mm"
include "cfv.mm"
include "com.mm"
include "eleq1.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "vex.mm"
include "elhf2.mm"
include "vtoclbg.mm"

theorem elhf2g
  let cA: class A
  let cV: class V
  let vx: setvar x


  assert |- ( A e. V -> ( A e. Hf <-> ( rank ` A ) e. _om ) )

  proof
    vx
    cv
    #
    chf
    wcel
    @0
    crnk
    cfv
    #
    com
    wcel
    cA
    chf
    wcel
    cA
    crnk
    cfv
    #
    com
    wcel
    vx
    cA
    cV
    @0
    cA
    chf
    eleq1
    @0
    cA
    wceq
    @1
    @2
    com
    @0
    cA
    crnk
    fveq2
    eleq1d
    @0
    vx
    vex
    elhf2
    vtoclbg
end
