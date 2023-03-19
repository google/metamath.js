include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cec.mm"
include "wbr.mm"
include "wb.mm"
include "cvv.mm"
include "elecALTV.mm"
include "el2v1.mm"
include "bi2anan9.mm"
include "exbidv.mm"

theorem exan3
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cR: class R
  let cV: class V
  let cW: class W

  disjoint A u
  disjoint B u
  disjoint V u
  disjoint W u
  assert |- ( ( A e. V /\ B e. W ) -> ( E. u ( A e. [ u ] R /\ B e. [ u ] R ) <-> E. u ( u R A /\ u R B ) ) )

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
    cA
    vu
    cv
    #
    cR
    cec
    #
    wcel
    #
    cB
    @3
    wcel
    #
    wa
    @2
    cA
    cR
    wbr
    #
    @2
    cB
    cR
    wbr
    #
    wa
    vu
    @0
    @4
    @6
    @1
    @5
    @7
    @0
    @4
    @6
    wb
    vu
    @2
    cA
    cR
    cvv
    cV
    elecALTV
    el2v1
    @1
    @5
    @7
    wb
    vu
    @2
    cB
    cR
    cvv
    cW
    elecALTV
    el2v1
    bi2anan9
    exbidv
end
