include "crab.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "df-rab.mm"
include "simpr.mm"
include "ss2abi.mm"
include "eqsstri.mm"

theorem rabssab
  let wph: wff ph
  let vx: setvar x
  let cA: class A


  assert |- { x e. A | ph } C_ { x | ph }

  proof
    wph
    vx
    cA
    crab
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
    wph
    vx
    cab
    wph
    vx
    cA
    df-rab
    @1
    wph
    vx
    @0
    wph
    simpr
    ss2abi
    eqsstri
end
