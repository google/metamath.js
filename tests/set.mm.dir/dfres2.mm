include "cres.mm"
include "cv.mm"
include "wcel.mm"
include "wbr.mm"
include "wa.mm"
include "copab.mm"
include "relres.mm"
include "relopab.mm"
include "cop.mm"
include "vex.mm"
include "brres.mm"
include "df-br.mm"
include "ancom.mm"
include "3bitr3i.mm"
include "weq.mm"
include "eleq1.mm"
include "breq1.mm"
include "anbi12d.mm"
include "breq2.mm"
include "anbi2d.mm"
include "opelopab.mm"
include "bitr4i.mm"
include "eqrelriiv.mm"

theorem dfres2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let vw: setvar w
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint R x
  disjoint R y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint R w
  disjoint R z
  assert |- ( R |` A ) = { <. x , y >. | ( x e. A /\ x R y ) }

  proof
    vz
    vw
    cR
    cA
    cres
    #
    vx
    cv
    #
    cA
    wcel
    #
    @1
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
    cR
    cA
    relres
    @5
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
    @0
    wcel
    #
    @7
    cA
    wcel
    #
    @7
    @8
    cR
    wbr
    #
    wa
    #
    @9
    @6
    wcel
    @7
    @8
    @0
    wbr
    @12
    @11
    wa
    @10
    @13
    @7
    @8
    cR
    cA
    vw
    vex
    #
    brres
    @7
    @8
    @0
    df-br
    @12
    @11
    ancom
    3bitr3i
    @5
    @11
    @7
    @3
    cR
    wbr
    #
    wa
    @13
    vx
    vy
    @7
    @8
    vz
    vex
    @14
    vx
    vz
    weq
    @2
    @11
    @4
    @15
    @1
    @7
    cA
    eleq1
    @1
    @7
    @3
    cR
    breq1
    anbi12d
    vy
    vw
    weq
    @15
    @12
    @11
    @3
    @8
    @7
    cR
    breq2
    anbi2d
    opelopab
    bitr4i
    eqrelriiv
end
