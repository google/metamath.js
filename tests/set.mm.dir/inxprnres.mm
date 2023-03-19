include "cres.mm"
include "crn.mm"
include "cxp.mm"
include "cin.mm"
include "cv.mm"
include "wcel.mm"
include "wbr.mm"
include "wa.mm"
include "copab.mm"
include "wrel.mm"
include "relxp.mm"
include "relin2.mm"
include "ax-mp.mm"
include "relopab.mm"
include "cop.mm"
include "wb.mm"
include "cvv.mm"
include "wceq.mm"
include "eleq1w.mm"
include "breq1.mm"
include "anbi12d.mm"
include "breq2.mm"
include "anbi2d.mm"
include "opelopabg.mm"
include "el2v.mm"
include "brinxprnres.mm"
include "elv.mm"
include "df-br.mm"
include "3bitr2ri.mm"
include "eqrelriiv.mm"

theorem inxprnres
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let vw: setvar w
  let vz: setvar z

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint R x
  disjoint R y
  disjoint A w
  disjoint A z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x z
  disjoint y z
  disjoint R w
  disjoint R z
  assert |- ( R i^i ( A X. ran ( R |` A ) ) ) = { <. x , y >. | ( x e. A /\ x R y ) }

  proof
    vz
    vw
    cR
    cA
    cR
    cA
    cres
    crn
    #
    cxp
    #
    cin
    #
    vx
    cv
    #
    cA
    wcel
    #
    @3
    vy
    cv
    #
    cR
    wbr
    #
    wa
    #
    vx
    vy
    copab
    #
    @1
    wrel
    @2
    wrel
    cA
    @0
    relxp
    cR
    @1
    relin2
    ax-mp
    @7
    vx
    vy
    relopab
    vz
    cv
    #
    vw
    cv
    #
    cop
    #
    @8
    wcel
    #
    @9
    cA
    wcel
    #
    @9
    @10
    cR
    wbr
    #
    wa
    #
    @9
    @10
    @2
    wbr
    #
    @11
    @2
    wcel
    @12
    @15
    wb
    vz
    vw
    @7
    @13
    @9
    @5
    cR
    wbr
    #
    wa
    @15
    vx
    vy
    @9
    @10
    cvv
    cvv
    @3
    @9
    wceq
    @4
    @13
    @6
    @17
    vx
    vz
    cA
    eleq1w
    @3
    @9
    @5
    cR
    breq1
    anbi12d
    @5
    @10
    wceq
    @17
    @14
    @13
    @5
    @10
    @9
    cR
    breq2
    anbi2d
    opelopabg
    el2v
    @16
    @15
    wb
    vw
    cA
    @9
    @10
    cR
    cvv
    brinxprnres
    elv
    @9
    @10
    @2
    df-br
    3bitr2ri
    eqrelriiv
end
