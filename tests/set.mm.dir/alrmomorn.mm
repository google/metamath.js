include "cv.mm"
include "wbr.mm"
include "crn.mm"
include "wrmo.mm"
include "wmo.mm"
include "wcel.mm"
include "wa.mm"
include "df-rmo.mm"
include "ccnv.mm"
include "cres.mm"
include "cnvresrn.mm"
include "breqi.mm"
include "wb.mm"
include "cvv.mm"
include "brresALTV.mm"
include "elv.mm"
include "brcnvg.mm"
include "el2v.mm"
include "anbi2i.mm"
include "bitri.mm"
include "3bitr3i.mm"
include "mobii.mm"
include "albii.mm"

theorem alrmomorn
  let vx: setvar x
  let vy: setvar y
  let cR: class R


  assert |- ( A. x E* y e. ran R x R y <-> A. x E* y x R y )

  proof
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    vy
    cR
    crn
    #
    wrmo
    #
    @2
    vy
    wmo
    #
    vx
    @4
    @1
    @3
    wcel
    #
    @2
    wa
    #
    vy
    wmo
    @5
    @2
    vy
    @3
    df-rmo
    @7
    @2
    vy
    @1
    @0
    cR
    ccnv
    #
    @3
    cres
    #
    wbr
    #
    @1
    @0
    @8
    wbr
    #
    @7
    @2
    @1
    @0
    @9
    @8
    cR
    cnvresrn
    breqi
    @10
    @6
    @11
    wa
    #
    @7
    @10
    @12
    wb
    vx
    @3
    @1
    @0
    @8
    cvv
    brresALTV
    elv
    @11
    @2
    @6
    @11
    @2
    wb
    vy
    vx
    @1
    @0
    cvv
    cvv
    cR
    brcnvg
    el2v
    #
    anbi2i
    bitri
    @13
    3bitr3i
    mobii
    bitri
    albii
end
