include "cv.mm"
include "cxp.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "copab.mm"
include "wcel.mm"
include "ccom.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "n0.mm"
include "elin.mm"
include "exbii.mm"
include "bitri.mm"
include "sylib.mm"
include "biantrud.mm"
include "brxp.mm"
include "ancom.mm"
include "anbi12i.mm"
include "an4.mm"
include "19.42v.mm"
include "3bitri.mm"
include "syl6rbbr.mm"
include "opabbidv.mm"
include "df-co.mm"
include "df-xp.mm"
include "3eqtr4g.mm"

theorem xpcogend
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vx: setvar x
  let vz: setvar z
  let vy: setvar y
  assume xpcogend.1: |- ( ph -> ( B i^i C ) =/= (/) )


  assert |- ( ph -> ( ( C X. D ) o. ( A X. B ) ) = ( A X. D ) )

  proof
    wph
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
    @1
    vz
    cv
    #
    cC
    cD
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
    @0
    cA
    wcel
    #
    @4
    cD
    wcel
    #
    wa
    #
    vx
    vz
    copab
    @5
    @2
    ccom
    cA
    cD
    cxp
    wph
    @8
    @11
    vx
    vz
    wph
    @11
    @11
    @1
    cB
    wcel
    #
    @1
    cC
    wcel
    #
    wa
    #
    vy
    wex
    #
    wa
    #
    @8
    wph
    @15
    @11
    wph
    cB
    cC
    cin
    #
    c0
    wne
    #
    @15
    xpcogend.1
    @18
    @1
    @17
    wcel
    #
    vy
    wex
    @15
    vy
    @17
    n0
    @19
    @14
    vy
    @1
    cB
    cC
    elin
    exbii
    bitri
    sylib
    biantrud
    @8
    @9
    @12
    wa
    #
    @10
    @13
    wa
    #
    wa
    #
    vy
    wex
    @11
    @14
    wa
    #
    vy
    wex
    @16
    @7
    @22
    vy
    @3
    @20
    @6
    @21
    @0
    @1
    cA
    cB
    brxp
    @6
    @13
    @10
    wa
    @21
    @1
    @4
    cC
    cD
    brxp
    @13
    @10
    ancom
    bitri
    anbi12i
    exbii
    @22
    @23
    vy
    @9
    @12
    @10
    @13
    an4
    exbii
    @11
    @14
    vy
    19.42v
    3bitri
    syl6rbbr
    opabbidv
    vx
    vz
    vy
    @5
    @2
    df-co
    vx
    vz
    cA
    cD
    df-xp
    3eqtr4g
end
