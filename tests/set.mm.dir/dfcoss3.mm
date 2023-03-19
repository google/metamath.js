include "cv.mm"
include "ccnv.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "copab.mm"
include "ccom.mm"
include "ccoss.mm"
include "wb.mm"
include "cvv.mm"
include "brcnvg.mm"
include "el2v.mm"
include "anbi1i.mm"
include "exbii.mm"
include "opabbii.mm"
include "df-co.mm"
include "df-coss.mm"
include "3eqtr4ri.mm"

theorem dfcoss3
  let cR: class R
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y


  assert |- ,~ R = ( R o. `' R )

  proof
    vx
    cv
    #
    vu
    cv
    #
    cR
    ccnv
    #
    wbr
    #
    @1
    vy
    cv
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
    wbr
    #
    @4
    wa
    #
    vu
    wex
    #
    vx
    vy
    copab
    cR
    @2
    ccom
    cR
    ccoss
    @6
    @9
    vx
    vy
    @5
    @8
    vu
    @3
    @7
    @4
    @3
    @7
    wb
    vx
    vu
    @0
    @1
    cvv
    cvv
    cR
    brcnvg
    el2v
    anbi1i
    exbii
    opabbii
    vx
    vy
    vu
    cR
    @2
    df-co
    vx
    vy
    vu
    cR
    df-coss
    3eqtr4ri
end
