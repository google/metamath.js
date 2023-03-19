include "cv.mm"
include "wss.mm"
include "cpw.mm"
include "sseq1.mm"
include "df-pw.mm"
include "elab2.mm"

theorem elpw
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume elpw.1: |- A e. _V


  assert |- ( A e. ~P B <-> A C_ B )

  proof
    vx
    cv
    #
    cB
    wss
    cA
    cB
    wss
    vx
    cA
    cB
    cpw
    elpw.1
    @0
    cA
    cB
    sseq1
    vx
    cB
    df-pw
    elab2
end
