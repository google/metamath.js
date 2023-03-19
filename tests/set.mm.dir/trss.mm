include "wtr.mm"
include "cv.mm"
include "wss.mm"
include "wral.mm"
include "wcel.mm"
include "wi.mm"
include "dftr3.mm"
include "sseq1.mm"
include "rspccv.mm"
include "sylbi.mm"

theorem trss
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( Tr A -> ( B e. A -> B C_ A ) )

  proof
    cA
    wtr
    vx
    cv
    #
    cA
    wss
    #
    vx
    cA
    wral
    cB
    cA
    wcel
    cB
    cA
    wss
    #
    wi
    vx
    cA
    dftr3
    @1
    @2
    vx
    cB
    cA
    @0
    cB
    cA
    sseq1
    rspccv
    sylbi
end
