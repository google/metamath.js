include "wtr.mm"
include "wcel.mm"
include "wss.mm"
include "cv.mm"
include "wi.mm"
include "wceq.mm"
include "eleq1.mm"
include "sseq1.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "wral.mm"
include "dftr3.mm"
include "rsp.mm"
include "sylbi.mm"
include "vtoclg.mm"
include "pm2.43b.mm"

theorem trssOLD
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( Tr A -> ( B e. A -> B C_ A ) )

  proof
    cA
    wtr
    #
    cB
    cA
    wcel
    #
    cB
    cA
    wss
    #
    @0
    vx
    cv
    #
    cA
    wcel
    #
    @3
    cA
    wss
    #
    wi
    #
    wi
    @0
    @1
    @2
    wi
    #
    wi
    vx
    cB
    cA
    @3
    cB
    wceq
    #
    @6
    @7
    @0
    @8
    @4
    @1
    @5
    @2
    @3
    cB
    cA
    eleq1
    @3
    cB
    cA
    sseq1
    imbi12d
    imbi2d
    @0
    @5
    vx
    cA
    wral
    @6
    vx
    cA
    dftr3
    @5
    vx
    cA
    rsp
    sylbi
    vtoclg
    pm2.43b
end
