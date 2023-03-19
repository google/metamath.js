include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "cv.mm"
include "con0.mm"
include "csdm.mm"
include "wbr.mm"
include "wa.mm"
include "cab.mm"
include "crab.mm"
include "wb.mm"
include "cardsdomel.mm"
include "ancoms.mm"
include "pm5.32da.mm"
include "cardon.mm"
include "oneli.mm"
include "pm4.71ri.mm"
include "syl6rbbr.mm"
include "abbi2dv.mm"
include "df-rab.mm"
include "syl6eqr.mm"

theorem cardval2
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( A e. dom card -> ( card ` A ) = { x e. On | x ~< A } )

  proof
    cA
    ccrd
    cdm
    wcel
    #
    cA
    ccrd
    cfv
    #
    vx
    cv
    #
    con0
    wcel
    #
    @2
    cA
    csdm
    wbr
    #
    wa
    #
    vx
    cab
    @4
    vx
    con0
    crab
    @0
    @5
    vx
    @1
    @0
    @5
    @3
    @2
    @1
    wcel
    #
    wa
    @6
    @0
    @3
    @4
    @6
    @3
    @0
    @4
    @6
    wb
    @2
    cA
    cardsdomel
    ancoms
    pm5.32da
    @6
    @3
    @1
    @2
    cA
    cardon
    oneli
    pm4.71ri
    syl6rbbr
    abbi2dv
    @4
    vx
    con0
    df-rab
    syl6eqr
end
