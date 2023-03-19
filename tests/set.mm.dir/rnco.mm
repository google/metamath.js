include "ccom.mm"
include "crn.mm"
include "cres.mm"
include "cv.mm"
include "wbr.mm"
include "wex.mm"
include "wcel.mm"
include "wa.mm"
include "vex.mm"
include "brco.mm"
include "exbii.mm"
include "excom.mm"
include "ancom.mm"
include "19.41v.mm"
include "elrn.mm"
include "anbi2i.mm"
include "3bitr4i.mm"
include "brres.mm"
include "bitr4i.mm"
include "3bitri.mm"
include "eqriv.mm"

theorem rnco
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C


  assert |- ran ( A o. B ) = ran ( A |` ran B )

  proof
    vy
    cA
    cB
    ccom
    #
    crn
    #
    cA
    cB
    crn
    #
    cres
    #
    crn
    #
    vx
    cv
    #
    vy
    cv
    #
    @0
    wbr
    #
    vx
    wex
    #
    vz
    cv
    #
    @6
    @3
    wbr
    #
    vz
    wex
    #
    @6
    @1
    wcel
    @6
    @4
    wcel
    @8
    @5
    @9
    cB
    wbr
    #
    @9
    @6
    cA
    wbr
    #
    wa
    #
    vz
    wex
    #
    vx
    wex
    @14
    vx
    wex
    #
    vz
    wex
    @11
    @7
    @15
    vx
    vz
    @5
    @6
    cA
    cB
    vx
    vex
    vy
    vex
    #
    brco
    exbii
    @14
    vx
    vz
    excom
    @16
    @10
    vz
    @16
    @13
    @9
    @2
    wcel
    #
    wa
    #
    @10
    @12
    vx
    wex
    #
    @13
    wa
    @13
    @20
    wa
    @16
    @19
    @20
    @13
    ancom
    @12
    @13
    vx
    19.41v
    @18
    @20
    @13
    vx
    @9
    cB
    vz
    vex
    elrn
    anbi2i
    3bitr4i
    @9
    @6
    cA
    @2
    @17
    brres
    bitr4i
    exbii
    3bitri
    vx
    @6
    @0
    @17
    elrn
    vz
    @6
    @3
    @17
    elrn
    3bitr4i
    eqriv
end
