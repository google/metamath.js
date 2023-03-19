include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wsbc.mm"
include "eqsbc3.mm"
include "eqcom.mm"
include "sbcbii.mm"
include "3bitr4g.mm"

theorem eqsbc3r
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V

  disjoint B x
  assert |- ( A e. V -> ( [. A / x ]. B = x <-> B = A ) )

  proof
    cA
    cV
    wcel
    vx
    cv
    #
    cB
    wceq
    #
    vx
    cA
    wsbc
    cA
    cB
    wceq
    cB
    @0
    wceq
    #
    vx
    cA
    wsbc
    cB
    cA
    wceq
    vx
    cA
    cB
    cV
    eqsbc3
    @2
    @1
    vx
    cA
    cB
    @0
    eqcom
    sbcbii
    cB
    cA
    eqcom
    3bitr4g
end
