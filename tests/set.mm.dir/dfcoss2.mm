include "ccoss.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "copab.mm"
include "cec.mm"
include "wcel.mm"
include "df-coss.mm"
include "wb.mm"
include "cvv.mm"
include "elecALTV.mm"
include "el2v.mm"
include "anbi12i.mm"
include "exbii.mm"
include "opabbii.mm"
include "eqtr4i.mm"

theorem dfcoss2
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cR: class R

  disjoint R u
  disjoint R x
  disjoint R y
  disjoint u x
  disjoint u y
  disjoint x y
  assert |- ,~ R = { <. x , y >. | E. u ( x e. [ u ] R /\ y e. [ u ] R ) }

  proof
    cR
    ccoss
    vu
    cv
    #
    vx
    cv
    #
    cR
    wbr
    #
    @0
    vy
    cv
    #
    cR
    wbr
    #
    wa
    #
    vu
    wex
    #
    vx
    vy
    copab
    @1
    @0
    cR
    cec
    #
    wcel
    #
    @3
    @7
    wcel
    #
    wa
    #
    vu
    wex
    #
    vx
    vy
    copab
    vx
    vy
    vu
    cR
    df-coss
    @11
    @6
    vx
    vy
    @10
    @5
    vu
    @8
    @2
    @9
    @4
    @8
    @2
    wb
    vu
    vx
    @0
    @1
    cR
    cvv
    cvv
    elecALTV
    el2v
    @9
    @4
    wb
    vu
    vy
    @0
    @3
    cR
    cvv
    cvv
    elecALTV
    el2v
    anbi12i
    exbii
    opabbii
    eqtr4i
end
