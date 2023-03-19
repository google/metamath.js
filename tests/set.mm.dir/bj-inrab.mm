include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "cin.mm"
include "crab.mm"
include "an4.mm"
include "elin.mm"
include "anbi1i.mm"
include "bitr4i.mm"
include "abbii.mm"
include "df-rab.mm"
include "ineq12i.mm"
include "inab.mm"
include "eqtri.mm"
include "3eqtr4i.mm"

theorem bj-inrab
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B


  assert |- ( { x e. A | ph } i^i { x e. B | ps } ) = { x e. ( A i^i B ) | ( ph /\ ps ) }

  proof
    vx
    cv
    #
    cA
    wcel
    #
    wph
    wa
    #
    @0
    cB
    wcel
    #
    wps
    wa
    #
    wa
    #
    vx
    cab
    #
    @0
    cA
    cB
    cin
    #
    wcel
    #
    wph
    wps
    wa
    #
    wa
    #
    vx
    cab
    wph
    vx
    cA
    crab
    #
    wps
    vx
    cB
    crab
    #
    cin
    #
    @9
    vx
    @7
    crab
    @5
    @10
    vx
    @5
    @1
    @3
    wa
    #
    @9
    wa
    @10
    @1
    wph
    @3
    wps
    an4
    @8
    @14
    @9
    @0
    cA
    cB
    elin
    anbi1i
    bitr4i
    abbii
    @13
    @2
    vx
    cab
    #
    @4
    vx
    cab
    #
    cin
    @6
    @11
    @15
    @12
    @16
    wph
    vx
    cA
    df-rab
    wps
    vx
    cB
    df-rab
    ineq12i
    @2
    @4
    vx
    inab
    eqtri
    @9
    vx
    @7
    df-rab
    3eqtr4i
end
