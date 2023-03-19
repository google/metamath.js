include "wcel.mm"
include "wa.mm"
include "ccnv.mm"
include "ccoss.mm"
include "wbr.mm"
include "cv.mm"
include "wex.mm"
include "brcoss.mm"
include "wb.mm"
include "cvv.mm"
include "brcnvg.mm"
include "el2v1.mm"
include "bi2anan9.mm"
include "exbidv.mm"
include "bitrd.mm"

theorem brcosscnv
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cV: class V
  let cW: class W

  disjoint A x
  disjoint B x
  disjoint R x
  disjoint V x
  disjoint W x
  assert |- ( ( A e. V /\ B e. W ) -> ( A ,~ `' R B <-> E. x ( A R x /\ B R x ) ) )

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
    cB
    cR
    ccnv
    #
    ccoss
    wbr
    vx
    cv
    #
    cA
    @3
    wbr
    #
    @4
    cB
    @3
    wbr
    #
    wa
    #
    vx
    wex
    cA
    @4
    cR
    wbr
    #
    cB
    @4
    cR
    wbr
    #
    wa
    #
    vx
    wex
    vx
    cA
    cB
    @3
    cV
    cW
    brcoss
    @2
    @7
    @10
    vx
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
    vx
    @4
    cA
    cvv
    cV
    cR
    brcnvg
    el2v1
    @1
    @6
    @9
    wb
    vx
    @4
    cB
    cvv
    cW
    cR
    brcnvg
    el2v1
    bi2anan9
    exbidv
    bitrd
end
