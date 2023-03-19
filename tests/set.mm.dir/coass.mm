include "ccom.mm"
include "relco.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "cop.mm"
include "wcel.mm"
include "excom.mm"
include "anass.mm"
include "2exbii.mm"
include "bitr4i.mm"
include "vex.mm"
include "brco.mm"
include "anbi2i.mm"
include "exbii.mm"
include "opelco.mm"
include "exdistr.mm"
include "3bitr4i.mm"
include "anbi1i.mm"
include "19.41v.mm"
include "eqrelriiv.mm"

theorem coass
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( ( A o. B ) o. C ) = ( A o. ( B o. C ) )

  proof
    vx
    vy
    cA
    cB
    ccom
    #
    cC
    ccom
    #
    cA
    cB
    cC
    ccom
    #
    ccom
    #
    @0
    cC
    relco
    cA
    @2
    relco
    vx
    cv
    #
    vz
    cv
    #
    cC
    wbr
    #
    @5
    vw
    cv
    #
    cB
    wbr
    #
    @7
    vy
    cv
    #
    cA
    wbr
    #
    wa
    #
    wa
    #
    vw
    wex
    vz
    wex
    #
    @6
    @8
    wa
    #
    @10
    wa
    #
    vz
    wex
    #
    vw
    wex
    #
    @4
    @9
    cop
    #
    @1
    wcel
    #
    @18
    @3
    wcel
    #
    @13
    @12
    vz
    wex
    vw
    wex
    @17
    @12
    vz
    vw
    excom
    @15
    @12
    vw
    vz
    @6
    @8
    @10
    anass
    2exbii
    bitr4i
    @6
    @5
    @9
    @0
    wbr
    #
    wa
    #
    vz
    wex
    @6
    @11
    vw
    wex
    #
    wa
    #
    vz
    wex
    @19
    @13
    @22
    @24
    vz
    @21
    @23
    @6
    vw
    @5
    @9
    cA
    cB
    vz
    vex
    vy
    vex
    #
    brco
    anbi2i
    exbii
    vz
    @4
    @9
    @0
    cC
    vx
    vex
    #
    @25
    opelco
    @6
    @11
    vz
    vw
    exdistr
    3bitr4i
    @4
    @7
    @2
    wbr
    #
    @10
    wa
    #
    vw
    wex
    @14
    vz
    wex
    #
    @10
    wa
    #
    vw
    wex
    @20
    @17
    @28
    @30
    vw
    @27
    @29
    @10
    vz
    @4
    @7
    cB
    cC
    @26
    vw
    vex
    brco
    anbi1i
    exbii
    vw
    @4
    @9
    cA
    @2
    @26
    @25
    opelco
    @16
    @30
    vw
    @14
    @10
    vz
    19.41v
    exbii
    3bitr4i
    3bitr4i
    eqrelriiv
end
