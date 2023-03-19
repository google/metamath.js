include "cv.mm"
include "cpw.mm"
include "wcel.mm"
include "wss.mm"
include "eleq1.mm"
include "sseq1.mm"
include "selpw.mm"
include "vtoclbg.mm"

theorem elpwg
  let cA: class A
  let cB: class B
  let cV: class V
  let vx: setvar x


  assert |- ( A e. V -> ( A e. ~P B <-> A C_ B ) )

  proof
    vx
    cv
    #
    cB
    cpw
    #
    wcel
    @0
    cB
    wss
    cA
    @1
    wcel
    cA
    cB
    wss
    vx
    cA
    cV
    @0
    cA
    @1
    eleq1
    @0
    cA
    cB
    sseq1
    vx
    cB
    selpw
    vtoclbg
end
