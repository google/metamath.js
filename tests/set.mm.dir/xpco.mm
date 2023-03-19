include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cxp.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "copab.mm"
include "wcel.mm"
include "ccom.mm"
include "n0.mm"
include "biimpi.mm"
include "biantrurd.mm"
include "ancom.mm"
include "anbi1i.mm"
include "brxp.mm"
include "anbi12i.mm"
include "anandi.mm"
include "3bitr4i.mm"
include "exbii.mm"
include "19.41v.mm"
include "bitr2i.mm"
include "syl6rbb.mm"
include "opabbidv.mm"
include "df-co.mm"
include "df-xp.mm"
include "3eqtr4g.mm"

theorem xpco
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( B =/= (/) -> ( ( B X. C ) o. ( A X. B ) ) = ( A X. C ) )

  proof
    cB
    c0
    wne
    #
    vx
    cv
    #
    vy
    cv
    #
    cA
    cB
    cxp
    #
    wbr
    #
    @2
    vz
    cv
    #
    cB
    cC
    cxp
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
    @1
    cA
    wcel
    #
    @5
    cC
    wcel
    #
    wa
    #
    vx
    vz
    copab
    @6
    @3
    ccom
    cA
    cC
    cxp
    @0
    @9
    @12
    vx
    vz
    @0
    @12
    @2
    cB
    wcel
    #
    vy
    wex
    #
    @12
    wa
    #
    @9
    @0
    @14
    @12
    @0
    @14
    vy
    cB
    n0
    biimpi
    biantrurd
    @9
    @13
    @12
    wa
    #
    vy
    wex
    @15
    @8
    @16
    vy
    @10
    @13
    wa
    #
    @13
    @11
    wa
    #
    wa
    @13
    @10
    wa
    #
    @18
    wa
    @8
    @16
    @17
    @19
    @18
    @10
    @13
    ancom
    anbi1i
    @4
    @17
    @7
    @18
    @1
    @2
    cA
    cB
    brxp
    @2
    @5
    cB
    cC
    brxp
    anbi12i
    @13
    @10
    @11
    anandi
    3bitr4i
    exbii
    @13
    @12
    vy
    19.41v
    bitr2i
    syl6rbb
    opabbidv
    vx
    vz
    vy
    @6
    @3
    df-co
    vx
    vz
    cA
    cC
    df-xp
    3eqtr4g
end
