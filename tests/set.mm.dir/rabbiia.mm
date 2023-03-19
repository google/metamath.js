include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "crab.mm"
include "pm5.32i.mm"
include "abbii.mm"
include "df-rab.mm"
include "3eqtr4i.mm"

theorem rabbiia
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume rabbiia.1: |- ( x e. A -> ( ph <-> ps ) )


  assert |- { x e. A | ph } = { x e. A | ps }

  proof
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
    @0
    wps
    wa
    #
    vx
    cab
    wph
    vx
    cA
    crab
    wps
    vx
    cA
    crab
    @1
    @2
    vx
    @0
    wph
    wps
    rabbiia.1
    pm5.32i
    abbii
    wph
    vx
    cA
    df-rab
    wps
    vx
    cA
    df-rab
    3eqtr4i
end
