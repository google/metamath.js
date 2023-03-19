include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wbr.mm"
include "w3a.mm"
include "wex.mm"
include "cab.mm"
include "wa.mm"
include "cxrn.mm"
include "crn.mm"
include "copab.mm"
include "3anass.mm"
include "3exbii.mm"
include "exrot3.mm"
include "19.42v.mm"
include "2exbii.mm"
include "3bitri.mm"
include "abbii.mm"
include "ccnv.mm"
include "cec.mm"
include "c0.mm"
include "wne.mm"
include "dfrn6.mm"
include "wcel.mm"
include "n0.mm"
include "wb.mm"
include "cvv.mm"
include "elec1cnvxrn2.mm"
include "elv.mm"
include "exbii.mm"
include "bitri.mm"
include "eqtri.mm"
include "df-opab.mm"
include "3eqtr4i.mm"

theorem rnxrn
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cR: class R
  let cS: class S
  let vw: setvar w

  disjoint R u
  disjoint R x
  disjoint R y
  disjoint u x
  disjoint u y
  disjoint x y
  disjoint S u
  disjoint S x
  disjoint S y
  disjoint R w
  disjoint u w
  disjoint w x
  disjoint w y
  disjoint S w
  assert |- ran ( R |X. S ) = { <. x , y >. | E. u ( u R x /\ u S y ) }

  proof
    vw
    cv
    #
    vx
    cv
    #
    vy
    cv
    #
    cop
    wceq
    #
    vu
    cv
    #
    @1
    cR
    wbr
    #
    @4
    @2
    cS
    wbr
    #
    w3a
    #
    vy
    wex
    vx
    wex
    #
    vu
    wex
    #
    vw
    cab
    #
    @3
    @5
    @6
    wa
    #
    vu
    wex
    #
    wa
    #
    vy
    wex
    vx
    wex
    #
    vw
    cab
    cR
    cS
    cxrn
    #
    crn
    #
    @12
    vx
    vy
    copab
    @9
    @14
    vw
    @9
    @3
    @11
    wa
    #
    vy
    wex
    vx
    wex
    vu
    wex
    @17
    vu
    wex
    #
    vy
    wex
    vx
    wex
    @14
    @7
    @17
    vu
    vx
    vy
    @3
    @5
    @6
    3anass
    3exbii
    @17
    vu
    vx
    vy
    exrot3
    @18
    @13
    vx
    vy
    @3
    @11
    vu
    19.42v
    2exbii
    3bitri
    abbii
    @16
    @0
    @15
    ccnv
    cec
    #
    c0
    wne
    #
    vw
    cab
    @10
    vw
    @15
    dfrn6
    @20
    @9
    vw
    @20
    @4
    @19
    wcel
    #
    vu
    wex
    @9
    vu
    @19
    n0
    @21
    @8
    vu
    @21
    @8
    wb
    vu
    vx
    vy
    @0
    @4
    cR
    cS
    cvv
    elec1cnvxrn2
    elv
    exbii
    bitri
    abbii
    eqtri
    @12
    vx
    vy
    vw
    df-opab
    3eqtr4i
end
