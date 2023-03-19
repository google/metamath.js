include "ccom.mm"
include "cima.mm"
include "cv.mm"
include "wbr.mm"
include "wrex.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "df-rex.mm"
include "vex.mm"
include "elima.mm"
include "rexcom4.mm"
include "r19.41v.mm"
include "exbii.mm"
include "bitri.mm"
include "brco.mm"
include "rexbii.mm"
include "anbi1i.mm"
include "3bitr4i.mm"
include "3bitr4ri.mm"
include "eqriv.mm"

theorem imaco
  let cA: class A
  let cB: class B
  let cC: class C
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A o. B ) " C ) = ( A " ( B " C ) )

  proof
    vx
    cA
    cB
    ccom
    #
    cC
    cima
    #
    cA
    cB
    cC
    cima
    #
    cima
    #
    vy
    cv
    #
    vx
    cv
    #
    cA
    wbr
    #
    vy
    @2
    wrex
    @4
    @2
    wcel
    #
    @6
    wa
    #
    vy
    wex
    #
    @5
    @3
    wcel
    @5
    @1
    wcel
    #
    @6
    vy
    @2
    df-rex
    vy
    @5
    cA
    @2
    vx
    vex
    #
    elima
    vz
    cv
    #
    @4
    cB
    wbr
    #
    @6
    wa
    #
    vy
    wex
    #
    vz
    cC
    wrex
    #
    @13
    vz
    cC
    wrex
    #
    @6
    wa
    #
    vy
    wex
    #
    @10
    @9
    @16
    @14
    vz
    cC
    wrex
    #
    vy
    wex
    @19
    @14
    vz
    vy
    cC
    rexcom4
    @20
    @18
    vy
    @13
    @6
    vz
    cC
    r19.41v
    exbii
    bitri
    @10
    @12
    @5
    @0
    wbr
    #
    vz
    cC
    wrex
    @16
    vz
    @5
    @0
    cC
    @11
    elima
    @21
    @15
    vz
    cC
    vy
    @12
    @5
    cA
    cB
    vz
    vex
    @11
    brco
    rexbii
    bitri
    @8
    @18
    vy
    @7
    @17
    @6
    vz
    @4
    cB
    cC
    vy
    vex
    elima
    anbi1i
    exbii
    3bitr4i
    3bitr4ri
    eqriv
end
