include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "crab.mm"
include "nfeq.mm"
include "eleq2.mm"
include "anbi1d.mm"
include "abbid.mm"
include "df-rab.mm"
include "3eqtr4g.mm"

theorem rabeqf
  param wph: wff ph
  param vx: setvar x
  param cA: class A
  param cB: class B
  assume rabeqf.1: |- F/_ x A
  assume rabeqf.2: |- F/_ x B


  assert |- ( A = B -> { x e. A | ph } = { x e. B | ph } )

  proof
    cA
    cB
    wceq
    #
    vx
    cv
    #
    cA
    wcel
    #
    wph
    wa
    #
    vx
    cab
    @1
    cB
    wcel
    #
    wph
    wa
    #
    vx
    cab
    wph
    vx
    cA
    crab
    wph
    vx
    cB
    crab
    @0
    @3
    @5
    vx
    vx
    cA
    cB
    rabeqf.1
    rabeqf.2
    nfeq
    @0
    @2
    @4
    wph
    cA
    cB
    @1
    eleq2
    anbi1d
    abbid
    wph
    vx
    cA
    df-rab
    wph
    vx
    cB
    df-rab
    3eqtr4g
end
