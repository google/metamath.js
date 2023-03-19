include "wrel.mm"
include "cv.mm"
include "wbr.mm"
include "cdm.mm"
include "wrmo.mm"
include "wmo.mm"
include "wcel.mm"
include "wa.mm"
include "df-rmo.mm"
include "cres.mm"
include "wb.mm"
include "cvv.mm"
include "brresALTV.mm"
include "elv.mm"
include "resdm.mm"
include "breqd.mm"
include "syl5bbr.mm"
include "mobidv.mm"
include "syl5bb.mm"
include "albidv.mm"

theorem alrmomodm
  let vx: setvar x
  let vu: setvar u
  let cR: class R

  disjoint R u
  disjoint R x
  assert |- ( Rel R -> ( A. x E* u e. dom R u R x <-> A. x E* u u R x ) )

  proof
    cR
    wrel
    #
    vu
    cv
    #
    vx
    cv
    #
    cR
    wbr
    #
    vu
    cR
    cdm
    #
    wrmo
    #
    @3
    vu
    wmo
    #
    vx
    @5
    @1
    @4
    wcel
    @3
    wa
    #
    vu
    wmo
    @0
    @6
    @3
    vu
    @4
    df-rmo
    @0
    @7
    @3
    vu
    @7
    @1
    @2
    cR
    @4
    cres
    #
    wbr
    #
    @0
    @3
    @9
    @7
    wb
    vx
    @4
    @1
    @2
    cR
    cvv
    brresALTV
    elv
    @0
    @8
    cR
    @1
    @2
    cR
    resdm
    breqd
    syl5bbr
    mobidv
    syl5bb
    albidv
end
