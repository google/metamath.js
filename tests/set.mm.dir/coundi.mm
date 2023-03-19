include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "copab.mm"
include "cun.mm"
include "ccom.mm"
include "wo.mm"
include "unopab.mm"
include "brun.mm"
include "anbi1i.mm"
include "andir.mm"
include "bitri.mm"
include "exbii.mm"
include "19.43.mm"
include "bitr2i.mm"
include "opabbii.mm"
include "eqtri.mm"
include "df-co.mm"
include "uneq12i.mm"
include "3eqtr4ri.mm"

theorem coundi
  let cA: class A
  let cB: class B
  let cC: class C
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A o. ( B u. C ) ) = ( ( A o. B ) u. ( A o. C ) )

  proof
    vx
    cv
    #
    vz
    cv
    #
    cB
    wbr
    #
    @1
    vy
    cv
    cA
    wbr
    #
    wa
    #
    vz
    wex
    #
    vx
    vy
    copab
    #
    @0
    @1
    cC
    wbr
    #
    @3
    wa
    #
    vz
    wex
    #
    vx
    vy
    copab
    #
    cun
    #
    @0
    @1
    cB
    cC
    cun
    #
    wbr
    #
    @3
    wa
    #
    vz
    wex
    #
    vx
    vy
    copab
    #
    cA
    cB
    ccom
    #
    cA
    cC
    ccom
    #
    cun
    cA
    @12
    ccom
    @11
    @5
    @9
    wo
    #
    vx
    vy
    copab
    @16
    @5
    @9
    vx
    vy
    unopab
    @19
    @15
    vx
    vy
    @15
    @4
    @8
    wo
    #
    vz
    wex
    @19
    @14
    @20
    vz
    @14
    @2
    @7
    wo
    #
    @3
    wa
    @20
    @13
    @21
    @3
    @0
    @1
    cB
    cC
    brun
    anbi1i
    @2
    @7
    @3
    andir
    bitri
    exbii
    @4
    @8
    vz
    19.43
    bitr2i
    opabbii
    eqtri
    @17
    @6
    @18
    @10
    vx
    vy
    vz
    cA
    cB
    df-co
    vx
    vy
    vz
    cA
    cC
    df-co
    uneq12i
    vx
    vy
    vz
    cA
    @12
    df-co
    3eqtr4ri
end
