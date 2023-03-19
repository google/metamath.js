include "cv.mm"
include "cpr.mm"
include "c0.mm"
include "wne.mm"
include "wceq.mm"
include "preq1.mm"
include "neeq1d.mm"
include "vex.mm"
include "prnz.mm"
include "vtoclg.mm"

theorem prnzgOLD
  let cA: class A
  let cB: class B
  let cV: class V
  let vx: setvar x


  assert |- ( A e. V -> { A , B } =/= (/) )

  proof
    vx
    cv
    #
    cB
    cpr
    #
    c0
    wne
    cA
    cB
    cpr
    #
    c0
    wne
    vx
    cA
    cV
    @0
    cA
    wceq
    @1
    @2
    c0
    @0
    cA
    cB
    preq1
    neeq1d
    @0
    cB
    vx
    vex
    prnz
    vtoclg
end
