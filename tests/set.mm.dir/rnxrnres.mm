include "cres.mm"
include "cxrn.mm"
include "crn.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "copab.mm"
include "wrex.mm"
include "rnxrn.mm"
include "wcel.mm"
include "wb.mm"
include "cvv.mm"
include "brresALTV.mm"
include "elv.mm"
include "anbi2i.mm"
include "an12.mm"
include "bitr4i.mm"
include "exbii.mm"
include "df-rex.mm"
include "opabbii.mm"
include "eqtri.mm"

theorem rnxrnres
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cA: class A
  let cR: class R
  let cS: class S

  disjoint A u
  disjoint A x
  disjoint A y
  disjoint u x
  disjoint u y
  disjoint x y
  disjoint R u
  disjoint R x
  disjoint R y
  disjoint S u
  disjoint S x
  disjoint S y
  assert |- ran ( R |X. ( S |` A ) ) = { <. x , y >. | E. u e. A ( u R x /\ u S y ) }

  proof
    cR
    cS
    cA
    cres
    #
    cxrn
    crn
    vu
    cv
    #
    vx
    cv
    cR
    wbr
    #
    @1
    vy
    cv
    #
    @0
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
    @2
    @1
    @3
    cS
    wbr
    #
    wa
    #
    vu
    cA
    wrex
    #
    vx
    vy
    copab
    vx
    vy
    vu
    cR
    @0
    rnxrn
    @6
    @9
    vx
    vy
    @6
    @1
    cA
    wcel
    #
    @8
    wa
    #
    vu
    wex
    @9
    @5
    @11
    vu
    @5
    @2
    @10
    @7
    wa
    #
    wa
    @11
    @4
    @12
    @2
    @4
    @12
    wb
    vy
    cA
    @1
    @3
    cS
    cvv
    brresALTV
    elv
    anbi2i
    @10
    @2
    @7
    an12
    bitr4i
    exbii
    @8
    vu
    cA
    df-rex
    bitr4i
    opabbii
    eqtri
end
