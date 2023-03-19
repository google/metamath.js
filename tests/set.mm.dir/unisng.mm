include "cv.mm"
include "csn.mm"
include "cuni.mm"
include "wceq.mm"
include "sneq.mm"
include "unieqd.mm"
include "id.mm"
include "eqeq12d.mm"
include "vex.mm"
include "unisn.mm"
include "vtoclg.mm"

theorem unisng
  let cA: class A
  let cV: class V
  let vx: setvar x


  assert |- ( A e. V -> U. { A } = A )

  proof
    vx
    cv
    #
    csn
    #
    cuni
    #
    @0
    wceq
    cA
    csn
    #
    cuni
    #
    cA
    wceq
    vx
    cA
    cV
    @0
    cA
    wceq
    #
    @2
    @4
    @0
    cA
    @5
    @1
    @3
    @0
    cA
    sneq
    unieqd
    @5
    id
    eqeq12d
    @0
    vx
    vex
    unisn
    vtoclg
end
