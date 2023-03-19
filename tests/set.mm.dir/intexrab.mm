include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "cint.mm"
include "cvv.mm"
include "wrex.mm"
include "crab.mm"
include "intexab.mm"
include "df-rex.mm"
include "df-rab.mm"
include "inteqi.mm"
include "eleq1i.mm"
include "3bitr4i.mm"

theorem intexrab
  let wph: wff ph
  let vx: setvar x
  let cA: class A


  assert |- ( E. x e. A ph <-> |^| { x e. A | ph } e. _V )

  proof
    vx
    cv
    cA
    wcel
    wph
    wa
    #
    vx
    wex
    @0
    vx
    cab
    #
    cint
    #
    cvv
    wcel
    wph
    vx
    cA
    wrex
    wph
    vx
    cA
    crab
    #
    cint
    #
    cvv
    wcel
    @0
    vx
    intexab
    wph
    vx
    cA
    df-rex
    @4
    @2
    cvv
    @3
    @1
    wph
    vx
    cA
    df-rab
    inteqi
    eleq1i
    3bitr4i
end
