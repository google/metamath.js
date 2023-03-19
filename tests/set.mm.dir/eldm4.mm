include "wcel.mm"
include "cdm.mm"
include "cv.mm"
include "wbr.mm"
include "wex.mm"
include "cec.mm"
include "eldmg.mm"
include "wb.mm"
include "cvv.mm"
include "elecALTV.mm"
include "el2v2.mm"
include "exbidv.mm"
include "bitr4d.mm"

theorem eldm4
  let vy: setvar y
  let cA: class A
  let cR: class R
  let cV: class V

  disjoint A y
  disjoint R y
  disjoint V y
  assert |- ( A e. V -> ( A e. dom R <-> E. y y e. [ A ] R ) )

  proof
    cA
    cV
    wcel
    #
    cA
    cR
    cdm
    wcel
    cA
    vy
    cv
    #
    cR
    wbr
    #
    vy
    wex
    @1
    cA
    cR
    cec
    wcel
    #
    vy
    wex
    vy
    cA
    cR
    cV
    eldmg
    @0
    @3
    @2
    vy
    @0
    @3
    @2
    wb
    vy
    cA
    @1
    cR
    cV
    cvv
    elecALTV
    el2v2
    exbidv
    bitr4d
end
