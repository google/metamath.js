include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "ccnv.mm"
include "wbr.mm"
include "wex.mm"
include "cec.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "ccoss.mm"
include "wb.mm"
include "cvv.mm"
include "brcnvg.mm"
include "el2v2.mm"
include "bi2anan9.mm"
include "exbidv.mm"
include "ecinn0.mm"
include "brcoss.mm"
include "3bitr4rd.mm"

theorem brcoss3
  let cA: class A
  let cB: class B
  let cR: class R
  let cV: class V
  let cW: class W
  let vu: setvar u


  assert |- ( ( A e. V /\ B e. W ) -> ( A ,~ R B <-> ( [ A ] `' R i^i [ B ] `' R ) =/= (/) ) )

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
    cA
    vu
    cv
    #
    cR
    ccnv
    #
    wbr
    #
    cB
    @3
    @4
    wbr
    #
    wa
    #
    vu
    wex
    @3
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
    #
    vu
    wex
    cA
    @4
    cec
    cB
    @4
    cec
    cin
    c0
    wne
    cA
    cB
    cR
    ccoss
    wbr
    @2
    @7
    @10
    vu
    @0
    @5
    @8
    @1
    @6
    @9
    @0
    @5
    @8
    wb
    vu
    cA
    @3
    cV
    cvv
    cR
    brcnvg
    el2v2
    @1
    @6
    @9
    wb
    vu
    cB
    @3
    cW
    cvv
    cR
    brcnvg
    el2v2
    bi2anan9
    exbidv
    vu
    cA
    cB
    @4
    cV
    cW
    ecinn0
    vu
    cA
    cB
    cR
    cV
    cW
    brcoss
    3bitr4rd
end
