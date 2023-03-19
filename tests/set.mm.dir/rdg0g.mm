include "c0.mm"
include "cv.mm"
include "crdg.mm"
include "cfv.mm"
include "wceq.mm"
include "rdgeq2.mm"
include "fveq1d.mm"
include "id.mm"
include "eqeq12d.mm"
include "vex.mm"
include "rdg0.mm"
include "vtoclg.mm"

theorem rdg0g
  let cA: class A
  let cC: class C
  let cF: class F
  let vx: setvar x


  assert |- ( A e. C -> ( rec ( F , A ) ` (/) ) = A )

  proof
    c0
    cF
    vx
    cv
    #
    crdg
    #
    cfv
    #
    @0
    wceq
    c0
    cF
    cA
    crdg
    #
    cfv
    #
    cA
    wceq
    vx
    cA
    cC
    @0
    cA
    wceq
    #
    @2
    @4
    @0
    cA
    @5
    c0
    @1
    @3
    @0
    cA
    cF
    rdgeq2
    fveq1d
    @5
    id
    eqeq12d
    @0
    cF
    vx
    vex
    rdg0
    vtoclg
end
