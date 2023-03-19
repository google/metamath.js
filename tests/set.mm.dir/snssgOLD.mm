include "cv.mm"
include "wcel.mm"
include "csn.mm"
include "wss.mm"
include "eleq1.mm"
include "wceq.mm"
include "sneq.mm"
include "sseq1d.mm"
include "vex.mm"
include "snss.mm"
include "vtoclbg.mm"

theorem snssgOLD
  let cA: class A
  let cB: class B
  let cV: class V
  let vx: setvar x


  assert |- ( A e. V -> ( A e. B <-> { A } C_ B ) )

  proof
    vx
    cv
    #
    cB
    wcel
    @0
    csn
    #
    cB
    wss
    cA
    cB
    wcel
    cA
    csn
    #
    cB
    wss
    vx
    cA
    cV
    @0
    cA
    cB
    eleq1
    @0
    cA
    wceq
    @1
    @2
    cB
    @0
    cA
    sneq
    sseq1d
    @0
    cB
    vx
    vex
    snss
    vtoclbg
end
