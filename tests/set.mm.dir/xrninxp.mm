include "cxrn.mm"
include "cxp.mm"
include "cin.mm"
include "cv.mm"
include "wcel.mm"
include "wbr.mm"
include "wa.mm"
include "copab.mm"
include "ccnv.mm"
include "cop.mm"
include "coprab.mm"
include "inxp2.mm"
include "w3a.mm"
include "df-3an.mm"
include "3anan12.mm"
include "bitr3i.mm"
include "opabbii.mm"
include "eqtri.mm"
include "cnvopab.mm"
include "wceq.mm"
include "breq2.mm"
include "anbi2d.mm"
include "dfoprab4.mm"
include "cnveqi.mm"
include "3eqtr2i.mm"

theorem xrninxp
  let vy: setvar y
  let vz: setvar z
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let vx: setvar x

  disjoint A u
  disjoint A y
  disjoint A z
  disjoint u y
  disjoint u z
  disjoint y z
  disjoint B u
  disjoint B y
  disjoint B z
  disjoint C u
  disjoint C y
  disjoint C z
  disjoint R u
  disjoint R y
  disjoint R z
  disjoint S u
  disjoint S y
  disjoint S z
  disjoint A x
  disjoint u x
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint C x
  disjoint R x
  disjoint S x
  assert |- ( ( R |X. S ) i^i ( A X. ( B X. C ) ) ) = `' { <. <. y , z >. , u >. | ( ( y e. B /\ z e. C ) /\ ( u e. A /\ u ( R |X. S ) <. y , z >. ) ) }

  proof
    cR
    cS
    cxrn
    #
    cA
    cB
    cC
    cxp
    #
    cxp
    cin
    #
    vx
    cv
    #
    @1
    wcel
    #
    vu
    cv
    #
    cA
    wcel
    #
    @5
    @3
    @0
    wbr
    #
    wa
    #
    wa
    #
    vu
    vx
    copab
    #
    @9
    vx
    vu
    copab
    #
    ccnv
    vy
    cv
    #
    cB
    wcel
    vz
    cv
    #
    cC
    wcel
    wa
    @6
    @5
    @12
    @13
    cop
    #
    @0
    wbr
    #
    wa
    #
    wa
    vy
    vz
    vu
    coprab
    #
    ccnv
    @2
    @6
    @4
    wa
    @7
    wa
    #
    vu
    vx
    copab
    @10
    vu
    vx
    cA
    @1
    @0
    inxp2
    @18
    @9
    vu
    vx
    @18
    @6
    @4
    @7
    w3a
    @9
    @6
    @4
    @7
    df-3an
    @6
    @4
    @7
    3anan12
    bitr3i
    opabbii
    eqtri
    @9
    vx
    vu
    cnvopab
    @11
    @17
    @8
    @16
    vy
    vz
    vu
    vx
    cB
    cC
    @3
    @14
    wceq
    @7
    @15
    @6
    @3
    @14
    @5
    @0
    breq2
    anbi2d
    dfoprab4
    cnveqi
    3eqtr2i
end
