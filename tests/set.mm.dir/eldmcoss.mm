include "ccoss.mm"
include "cdm.mm"
include "wcel.mm"
include "ccnv.mm"
include "cv.mm"
include "wbr.mm"
include "wex.mm"
include "dmcoss3.mm"
include "eleq2i.mm"
include "eldmcnv.mm"
include "syl5bb.mm"

theorem eldmcoss
  let vu: setvar u
  let cA: class A
  let cR: class R
  let cV: class V

  disjoint A u
  disjoint R u
  disjoint V u
  assert |- ( A e. V -> ( A e. dom ,~ R <-> E. u u R A ) )

  proof
    cA
    cR
    ccoss
    cdm
    #
    wcel
    cA
    cR
    ccnv
    cdm
    #
    wcel
    cA
    cV
    wcel
    vu
    cv
    cA
    cR
    wbr
    vu
    wex
    @0
    @1
    cA
    cR
    dmcoss3
    eleq2i
    vu
    cA
    cR
    cV
    eldmcnv
    syl5bb
end
