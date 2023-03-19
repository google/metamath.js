include "cv.mm"
include "wceq.mm"
include "wo.mm"
include "cpr.mm"
include "eqeq1.mm"
include "orbi12d.mm"
include "dfpr2.mm"
include "elab2g.mm"

theorem elprg
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let vx: setvar x


  assert |- ( A e. V -> ( A e. { B , C } <-> ( A = B \/ A = C ) ) )

  proof
    vx
    cv
    #
    cB
    wceq
    #
    @0
    cC
    wceq
    #
    wo
    cA
    cB
    wceq
    #
    cA
    cC
    wceq
    #
    wo
    vx
    cA
    cB
    cC
    cpr
    cV
    @0
    cA
    wceq
    @1
    @3
    @2
    @4
    @0
    cA
    cB
    eqeq1
    @0
    cA
    cC
    eqeq1
    orbi12d
    vx
    cB
    cC
    dfpr2
    elab2g
end
