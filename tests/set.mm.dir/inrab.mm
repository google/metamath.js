include "crab.mm"
include "cin.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "df-rab.mm"
include "ineq12i.mm"
include "inab.mm"
include "anandi.mm"
include "abbii.mm"
include "eqtr4i.mm"

theorem inrab
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A


  assert |- ( { x e. A | ph } i^i { x e. A | ps } ) = { x e. A | ( ph /\ ps ) }

  proof
    wph
    vx
    cA
    crab
    #
    wps
    vx
    cA
    crab
    #
    cin
    vx
    cv
    cA
    wcel
    #
    wph
    wa
    #
    vx
    cab
    #
    @2
    wps
    wa
    #
    vx
    cab
    #
    cin
    #
    wph
    wps
    wa
    #
    vx
    cA
    crab
    #
    @0
    @4
    @1
    @6
    wph
    vx
    cA
    df-rab
    wps
    vx
    cA
    df-rab
    ineq12i
    @9
    @2
    @8
    wa
    #
    vx
    cab
    #
    @7
    @8
    vx
    cA
    df-rab
    @7
    @3
    @5
    wa
    #
    vx
    cab
    @11
    @3
    @5
    vx
    inab
    @10
    @12
    vx
    @2
    wph
    wps
    anandi
    abbii
    eqtr4i
    eqtr4i
    eqtr4i
end
