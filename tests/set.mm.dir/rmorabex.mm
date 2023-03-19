include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wmo.mm"
include "cab.mm"
include "cvv.mm"
include "wrmo.mm"
include "crab.mm"
include "moabex.mm"
include "df-rmo.mm"
include "df-rab.mm"
include "eleq1i.mm"
include "3imtr4i.mm"

theorem rmorabex
  let wph: wff ph
  let vx: setvar x
  let cA: class A


  assert |- ( E* x e. A ph -> { x e. A | ph } e. _V )

  proof
    vx
    cv
    cA
    wcel
    wph
    wa
    #
    vx
    wmo
    @0
    vx
    cab
    #
    cvv
    wcel
    wph
    vx
    cA
    wrmo
    wph
    vx
    cA
    crab
    #
    cvv
    wcel
    @0
    vx
    moabex
    wph
    vx
    cA
    df-rmo
    @2
    @1
    cvv
    wph
    vx
    cA
    df-rab
    eleq1i
    3imtr4i
end
