include "wcel.mm"
include "ccnv.mm"
include "cdm.mm"
include "cv.mm"
include "wbr.mm"
include "wex.mm"
include "eldmg.mm"
include "wb.mm"
include "cvv.mm"
include "brcnvg.mm"
include "el2v2.mm"
include "exbidv.mm"
include "bitrd.mm"

theorem eldmcnv
  let vu: setvar u
  let cA: class A
  let cR: class R
  let cV: class V

  disjoint A u
  disjoint R u
  disjoint V u
  assert |- ( A e. V -> ( A e. dom `' R <-> E. u u R A ) )

  proof
    cA
    cV
    wcel
    #
    cA
    cR
    ccnv
    #
    cdm
    wcel
    cA
    vu
    cv
    #
    @1
    wbr
    #
    vu
    wex
    @2
    cA
    cR
    wbr
    #
    vu
    wex
    vu
    cA
    @1
    cV
    eldmg
    @0
    @3
    @4
    vu
    @0
    @3
    @4
    wb
    vu
    cA
    @2
    cV
    cvv
    cR
    brcnvg
    el2v2
    exbidv
    bitrd
end
