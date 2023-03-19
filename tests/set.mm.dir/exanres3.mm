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
include "rexbidv.mm"

theorem exanres3
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cV: class V
  let cW: class W

  disjoint B u
  disjoint C u
  disjoint V u
  disjoint W u
  assert |- ( ( B e. V /\ C e. W ) -> ( E. u e. A ( B e. [ u ] R /\ C e. [ u ] S ) <-> E. u e. A ( u R B /\ u S C ) ) )

  proof
    cB
    cV
    wcel
    #
    cC
    cW
    wcel
    #
    wa
    cB
    vu
    cv
    #
    cR
    cec
    wcel
    #
    cC
    @2
    cS
    cec
    wcel
    #
    wa
    @2
    cB
    cR
    wbr
    #
    @2
    cC
    cS
    wbr
    #
    wa
    vu
    cA
    @0
    @3
    @5
    @1
    @4
    @6
    @0
    @3
    @5
    wb
    vu
    @2
    cB
    cR
    cvv
    cV
    elecALTV
    el2v1
    @1
    @4
    @6
    wb
    vu
    @2
    cC
    cS
    cvv
    cW
    elecALTV
    el2v1
    bi2anan9
    rexbidv
end
