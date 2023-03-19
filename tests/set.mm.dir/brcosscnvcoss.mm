include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "wex.mm"
include "ccoss.mm"
include "wb.mm"
include "exancom.mm"
include "a1i.mm"
include "brcoss.mm"
include "ancoms.mm"
include "3bitr4d.mm"

theorem brcosscnvcoss
  let cA: class A
  let cB: class B
  let cR: class R
  let cV: class V
  let cW: class W
  let vu: setvar u


  assert |- ( ( A e. V /\ B e. W ) -> ( A ,~ R B <-> B ,~ R A ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    wa
    #
    vu
    cv
    #
    cA
    cR
    wbr
    #
    @3
    cB
    cR
    wbr
    #
    wa
    vu
    wex
    #
    @5
    @4
    wa
    vu
    wex
    #
    cA
    cB
    cR
    ccoss
    #
    wbr
    cB
    cA
    @8
    wbr
    #
    @6
    @7
    wb
    @2
    @4
    @5
    vu
    exancom
    a1i
    vu
    cA
    cB
    cR
    cV
    cW
    brcoss
    @1
    @0
    @9
    @7
    wb
    vu
    cB
    cA
    cR
    cW
    cV
    brcoss
    ancoms
    3bitr4d
end
