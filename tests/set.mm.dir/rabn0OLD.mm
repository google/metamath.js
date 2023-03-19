include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "c0.mm"
include "wne.mm"
include "wex.mm"
include "crab.mm"
include "wrex.mm"
include "abn0.mm"
include "df-rab.mm"
include "neeq1i.mm"
include "df-rex.mm"
include "3bitr4i.mm"

theorem rabn0OLD
  let wph: wff ph
  let vx: setvar x
  let cA: class A


  assert |- ( { x e. A | ph } =/= (/) <-> E. x e. A ph )

  proof
    vx
    cv
    cA
    wcel
    wph
    wa
    #
    vx
    cab
    #
    c0
    wne
    @0
    vx
    wex
    wph
    vx
    cA
    crab
    #
    c0
    wne
    wph
    vx
    cA
    wrex
    @0
    vx
    abn0
    @2
    @1
    c0
    wph
    vx
    cA
    df-rab
    neeq1i
    wph
    vx
    cA
    df-rex
    3bitr4i
end
