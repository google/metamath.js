include "cv.mm"
include "csn.mm"
include "wceq.mm"
include "wi.mm"
include "sneq.mm"
include "eqeq1d.mm"
include "eqeq1.mm"
include "imbi12d.mm"
include "vex.mm"
include "sneqr.mm"
include "vtoclg.mm"

theorem sneqrgOLD
  let cA: class A
  let cB: class B
  let cV: class V
  let vx: setvar x


  assert |- ( A e. V -> ( { A } = { B } -> A = B ) )

  proof
    vx
    cv
    #
    csn
    #
    cB
    csn
    #
    wceq
    #
    @0
    cB
    wceq
    #
    wi
    cA
    csn
    #
    @2
    wceq
    #
    cA
    cB
    wceq
    #
    wi
    vx
    cA
    cV
    @0
    cA
    wceq
    #
    @3
    @6
    @4
    @7
    @8
    @1
    @5
    @2
    @0
    cA
    sneq
    eqeq1d
    @0
    cA
    cB
    eqeq1
    imbi12d
    @0
    cB
    vx
    vex
    sneqr
    vtoclg
end
