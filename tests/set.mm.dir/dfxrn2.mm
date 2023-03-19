include "cxrn.mm"
include "cv.mm"
include "wbr.mm"
include "copab.mm"
include "cop.mm"
include "coprab.mm"
include "ccnv.mm"
include "wa.mm"
include "wrel.mm"
include "wceq.mm"
include "xrnrel.mm"
include "dfrel4v.mm"
include "mpbi.mm"
include "breq2.mm"
include "cvv.mm"
include "cxp.mm"
include "wcel.mm"
include "w3a.mm"
include "wex.mm"
include "wb.mm"
include "brxrn2.mm"
include "elv.mm"
include "brxrn.mm"
include "el3v.mm"
include "anbi2i.mm"
include "3anass.mm"
include "bitr4i.mm"
include "2exbii.mm"
include "copsex2gb.mm"
include "3bitr2i.mm"
include "simplbi.mm"
include "cnvoprab.mm"
include "oprabbii.mm"
include "cnveqi.mm"
include "3eqtr2i.mm"

theorem dfxrn2
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cR: class R
  let cS: class S
  let vz: setvar z

  disjoint R u
  disjoint R x
  disjoint R y
  disjoint u x
  disjoint u y
  disjoint x y
  disjoint S u
  disjoint S x
  disjoint S y
  disjoint R z
  disjoint u z
  disjoint x z
  disjoint y z
  disjoint S z
  assert |- ( R |X. S ) = `' { <. <. x , y >. , u >. | ( u R x /\ u S y ) }

  proof
    cR
    cS
    cxrn
    #
    vu
    cv
    #
    vz
    cv
    #
    @0
    wbr
    #
    vu
    vz
    copab
    #
    @1
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    @0
    wbr
    #
    vx
    vy
    vu
    coprab
    #
    ccnv
    @1
    @5
    cR
    wbr
    #
    @1
    @6
    cS
    wbr
    #
    wa
    #
    vx
    vy
    vu
    coprab
    #
    ccnv
    @0
    wrel
    @0
    @4
    wceq
    cR
    cS
    xrnrel
    vu
    vz
    @0
    dfrel4v
    mpbi
    @8
    @3
    vx
    vy
    vu
    vz
    @2
    @7
    @1
    @0
    breq2
    #
    @3
    @2
    cvv
    cvv
    cxp
    wcel
    #
    @3
    @3
    @2
    @7
    wceq
    #
    @10
    @11
    w3a
    #
    vy
    wex
    vx
    wex
    #
    @16
    @8
    wa
    #
    vy
    wex
    vx
    wex
    @15
    @3
    wa
    @3
    @18
    wb
    vu
    vx
    vy
    @1
    @2
    cR
    cS
    cvv
    brxrn2
    elv
    @19
    @17
    vx
    vy
    @19
    @16
    @12
    wa
    @17
    @8
    @12
    @16
    @8
    @12
    wb
    vu
    vx
    vy
    @1
    @5
    @6
    cR
    cS
    cvv
    cvv
    cvv
    brxrn
    el3v
    #
    anbi2i
    @16
    @10
    @11
    3anass
    bitr4i
    2exbii
    @3
    @8
    vx
    vy
    @2
    @14
    copsex2gb
    3bitr2i
    simplbi
    cnvoprab
    @9
    @13
    @8
    @12
    vx
    vy
    vu
    @20
    oprabbii
    cnveqi
    3eqtr2i
end
