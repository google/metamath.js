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
include "anbi2i.mm"
include "andi.mm"
include "bitri.mm"
include "exbii.mm"
include "19.43.mm"
include "bitr2i.mm"
include "opabbii.mm"
include "eqtri.mm"
include "df-co.mm"
include "uneq12i.mm"
include "3eqtr4ri.mm"

theorem coundir
  let cA: class A
  let cB: class B
  let cC: class C
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A u. B ) o. C ) = ( ( A o. C ) u. ( B o. C ) )

  proof
    vx
    cv
    vy
    cv
    #
    cC
    wbr
    #
    @0
    vz
    cv
    #
    cA
    wbr
    #
    wa
    #
    vy
    wex
    #
    vx
    vz
    copab
    #
    @1
    @0
    @2
    cB
    wbr
    #
    wa
    #
    vy
    wex
    #
    vx
    vz
    copab
    #
    cun
    #
    @1
    @0
    @2
    cA
    cB
    cun
    #
    wbr
    #
    wa
    #
    vy
    wex
    #
    vx
    vz
    copab
    #
    cA
    cC
    ccom
    #
    cB
    cC
    ccom
    #
    cun
    @12
    cC
    ccom
    @11
    @5
    @9
    wo
    #
    vx
    vz
    copab
    @16
    @5
    @9
    vx
    vz
    unopab
    @19
    @15
    vx
    vz
    @15
    @4
    @8
    wo
    #
    vy
    wex
    @19
    @14
    @20
    vy
    @14
    @1
    @3
    @7
    wo
    #
    wa
    @20
    @13
    @21
    @1
    @0
    @2
    cA
    cB
    brun
    anbi2i
    @1
    @3
    @7
    andi
    bitri
    exbii
    @4
    @8
    vy
    19.43
    bitr2i
    opabbii
    eqtri
    @17
    @6
    @18
    @10
    vx
    vz
    vy
    cA
    cC
    df-co
    vx
    vz
    vy
    cB
    cC
    df-co
    uneq12i
    vx
    vz
    vy
    @12
    cC
    df-co
    3eqtr4ri
end
