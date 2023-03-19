include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "copab.mm"
include "cin.mm"
include "cxp.mm"
include "inopab.mm"
include "an4.mm"
include "elin.mm"
include "anbi12i.mm"
include "bitr4i.mm"
include "opabbii.mm"
include "eqtri.mm"
include "df-xp.mm"
include "ineq12i.mm"
include "3eqtr4i.mm"

theorem inxp
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( A X. B ) i^i ( C X. D ) ) = ( ( A i^i C ) X. ( B i^i D ) )

  proof
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    #
    cB
    wcel
    #
    wa
    #
    vx
    vy
    copab
    #
    @0
    cC
    wcel
    #
    @2
    cD
    wcel
    #
    wa
    #
    vx
    vy
    copab
    #
    cin
    #
    @0
    cA
    cC
    cin
    #
    wcel
    #
    @2
    cB
    cD
    cin
    #
    wcel
    #
    wa
    #
    vx
    vy
    copab
    #
    cA
    cB
    cxp
    #
    cC
    cD
    cxp
    #
    cin
    @11
    @13
    cxp
    @10
    @4
    @8
    wa
    #
    vx
    vy
    copab
    @16
    @4
    @8
    vx
    vy
    inopab
    @19
    @15
    vx
    vy
    @19
    @1
    @6
    wa
    #
    @3
    @7
    wa
    #
    wa
    @15
    @1
    @3
    @6
    @7
    an4
    @12
    @20
    @14
    @21
    @0
    cA
    cC
    elin
    @2
    cB
    cD
    elin
    anbi12i
    bitr4i
    opabbii
    eqtri
    @17
    @5
    @18
    @9
    vx
    vy
    cA
    cB
    df-xp
    vx
    vy
    cC
    cD
    df-xp
    ineq12i
    vx
    vy
    @11
    @13
    df-xp
    3eqtr4i
end
