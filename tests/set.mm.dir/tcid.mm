include "wcel.mm"
include "cv.mm"
include "wss.mm"
include "wtr.mm"
include "wa.mm"
include "cab.mm"
include "cint.mm"
include "ctc.mm"
include "cfv.mm"
include "ssmin.mm"
include "tcvalg.mm"
include "syl5sseqr.mm"

theorem tcid
  let cA: class A
  let cV: class V
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. V -> A C_ ( TC ` A ) )

  proof
    cA
    cV
    wcel
    cA
    vx
    cv
    #
    wss
    @0
    wtr
    #
    wa
    vx
    cab
    cint
    cA
    cA
    ctc
    cfv
    @1
    vx
    cA
    ssmin
    vx
    cA
    cV
    tcvalg
    syl5sseqr
end
