include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "crab.mm"
include "ancom.mm"
include "abbii.mm"
include "df-rab.mm"
include "3eqtr4i.mm"

theorem rabswap
  let vx: setvar x
  let cA: class A
  let cB: class B


  assert |- { x e. A | x e. B } = { x e. B | x e. A }

  proof
    vx
    cv
    #
    cA
    wcel
    #
    @0
    cB
    wcel
    #
    wa
    #
    vx
    cab
    @2
    @1
    wa
    #
    vx
    cab
    @2
    vx
    cA
    crab
    @1
    vx
    cB
    crab
    @3
    @4
    vx
    @1
    @2
    ancom
    abbii
    @2
    vx
    cA
    df-rab
    @1
    vx
    cB
    df-rab
    3eqtr4i
end
