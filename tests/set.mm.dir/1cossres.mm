include "cres.mm"
include "ccoss.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "copab.mm"
include "wrex.mm"
include "df-coss.mm"
include "wcel.mm"
include "df-rex.mm"
include "anandi.mm"
include "wb.mm"
include "cvv.mm"
include "brresALTV.mm"
include "elv.mm"
include "anbi12i.mm"
include "bitr4i.mm"
include "exbii.mm"
include "bitri.mm"
include "opabbii.mm"
include "eqtr4i.mm"

theorem 1cossres
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cA: class A
  let cR: class R

  disjoint A u
  disjoint A x
  disjoint A y
  disjoint u x
  disjoint u y
  disjoint x y
  disjoint R u
  disjoint R x
  disjoint R y
  assert |- ,~ ( R |` A ) = { <. x , y >. | E. u e. A ( u R x /\ u R y ) }

  proof
    cR
    cA
    cres
    #
    ccoss
    vu
    cv
    #
    vx
    cv
    #
    @0
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
    @1
    @2
    cR
    wbr
    #
    @1
    @4
    cR
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
    @0
    df-coss
    @11
    @7
    vx
    vy
    @11
    @1
    cA
    wcel
    #
    @10
    wa
    #
    vu
    wex
    @7
    @10
    vu
    cA
    df-rex
    @13
    @6
    vu
    @13
    @12
    @8
    wa
    #
    @12
    @9
    wa
    #
    wa
    @6
    @12
    @8
    @9
    anandi
    @3
    @14
    @5
    @15
    @3
    @14
    wb
    vx
    cA
    @1
    @2
    cR
    cvv
    brresALTV
    elv
    @5
    @15
    wb
    vy
    cA
    @1
    @4
    cR
    cvv
    brresALTV
    elv
    anbi12i
    bitr4i
    exbii
    bitri
    opabbii
    eqtr4i
end
