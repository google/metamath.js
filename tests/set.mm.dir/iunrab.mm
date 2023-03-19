include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "ciun.mm"
include "wrex.mm"
include "crab.mm"
include "iunab.mm"
include "wceq.mm"
include "df-rab.mm"
include "a1i.mm"
include "iuneq2i.mm"
include "r19.42v.mm"
include "abbii.mm"
include "eqtr4i.mm"
include "3eqtr4i.mm"

theorem iunrab
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B

  disjoint A y
  disjoint x y
  disjoint B x
  assert |- U_ x e. A { y e. B | ph } = { y e. B | E. x e. A ph }

  proof
    vx
    cA
    vy
    cv
    cB
    wcel
    #
    wph
    wa
    #
    vy
    cab
    #
    ciun
    @1
    vx
    cA
    wrex
    #
    vy
    cab
    #
    vx
    cA
    wph
    vy
    cB
    crab
    #
    ciun
    wph
    vx
    cA
    wrex
    #
    vy
    cB
    crab
    #
    @1
    vx
    vy
    cA
    iunab
    vx
    cA
    @5
    @2
    @5
    @2
    wceq
    vx
    cv
    cA
    wcel
    wph
    vy
    cB
    df-rab
    a1i
    iuneq2i
    @7
    @0
    @6
    wa
    #
    vy
    cab
    @4
    @6
    vy
    cB
    df-rab
    @3
    @8
    vy
    @0
    wph
    vx
    cA
    r19.42v
    abbii
    eqtr4i
    3eqtr4i
end
