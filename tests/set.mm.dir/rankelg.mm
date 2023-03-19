include "wcel.mm"
include "crnk.mm"
include "cfv.mm"
include "cv.mm"
include "wi.mm"
include "wceq.mm"
include "eleq2.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "imbi12d.mm"
include "vex.mm"
include "rankel.mm"
include "vtoclg.mm"
include "imp.mm"

theorem rankelg
  let cA: class A
  let cB: class B
  let cV: class V
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( B e. V /\ A e. B ) -> ( rank ` A ) e. ( rank ` B ) )

  proof
    cB
    cV
    wcel
    cA
    cB
    wcel
    #
    cA
    crnk
    cfv
    #
    cB
    crnk
    cfv
    #
    wcel
    #
    cA
    vy
    cv
    #
    wcel
    #
    @1
    @4
    crnk
    cfv
    #
    wcel
    #
    wi
    @0
    @3
    wi
    vy
    cB
    cV
    @4
    cB
    wceq
    #
    @5
    @0
    @7
    @3
    @4
    cB
    cA
    eleq2
    @8
    @6
    @2
    @1
    @4
    cB
    crnk
    fveq2
    eleq2d
    imbi12d
    cA
    @4
    vy
    vex
    rankel
    vtoclg
    imp
end
