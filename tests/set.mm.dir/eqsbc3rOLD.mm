include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wsbc.mm"
include "eqcom.mm"
include "sbcbii.mm"
include "biimpi.mm"
include "eqsbc3.mm"
include "syl5ib.mm"
include "syl6ib.mm"
include "idd.mm"
include "syl6ibr.mm"
include "sylibrd.mm"
include "impbid.mm"

theorem eqsbc3rOLD
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
    #
    cB
    vx
    cv
    #
    wceq
    #
    vx
    cA
    wsbc
    #
    cB
    cA
    wceq
    #
    @0
    @3
    cA
    cB
    wceq
    #
    @4
    @3
    @1
    cB
    wceq
    #
    vx
    cA
    wsbc
    #
    @0
    @5
    @3
    @7
    @2
    @6
    vx
    cA
    cB
    @1
    eqcom
    sbcbii
    #
    biimpi
    vx
    cA
    cB
    cV
    eqsbc3
    #
    syl5ib
    cA
    cB
    eqcom
    #
    syl6ib
    @0
    @4
    @7
    @3
    @0
    @4
    @5
    @7
    @0
    @4
    @4
    @5
    @0
    @4
    idd
    @10
    syl6ibr
    @9
    sylibrd
    @8
    syl6ibr
    impbid
end
