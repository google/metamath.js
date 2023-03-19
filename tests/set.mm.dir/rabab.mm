include "cvv.mm"
include "crab.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "df-rab.mm"
include "vex.mm"
include "biantrur.mm"
include "abbii.mm"
include "eqtr4i.mm"

theorem rabab
  let wph: wff ph
  let vx: setvar x


  assert |- { x e. _V | ph } = { x | ph }

  proof
    wph
    vx
    cvv
    crab
    vx
    cv
    cvv
    wcel
    #
    wph
    wa
    #
    vx
    cab
    wph
    vx
    cab
    wph
    vx
    cvv
    df-rab
    wph
    @1
    vx
    @0
    wph
    vx
    vex
    biantrur
    abbii
    eqtr4i
end
