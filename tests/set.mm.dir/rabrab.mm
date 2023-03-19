include "cv.mm"
include "crab.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "rabid.mm"
include "anbi1i.mm"
include "anass.mm"
include "bitri.mm"
include "abbii.mm"
include "df-rab.mm"
include "3eqtr4i.mm"

theorem rabrab
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A


  assert |- { x e. { x e. A | ph } | ps } = { x e. A | ( ph /\ ps ) }

  proof
    vx
    cv
    #
    wph
    vx
    cA
    crab
    #
    wcel
    #
    wps
    wa
    #
    vx
    cab
    @0
    cA
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
    wps
    vx
    @1
    crab
    @5
    vx
    cA
    crab
    @3
    @6
    vx
    @3
    @4
    wph
    wa
    #
    wps
    wa
    @6
    @2
    @7
    wps
    wph
    vx
    cA
    rabid
    anbi1i
    @4
    wph
    wps
    anass
    bitri
    abbii
    wps
    vx
    @1
    df-rab
    @5
    vx
    cA
    df-rab
    3eqtr4i
end
