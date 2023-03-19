include "ciun.mm"
include "crab.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "wrex.mm"
include "eliun.mm"
include "anbi1i.mm"
include "r19.41v.mm"
include "bitr4i.mm"
include "abbii.mm"
include "df-rab.mm"
include "iunab.mm"
include "3eqtr4i.mm"
include "wceq.mm"
include "a1i.mm"
include "iuneq2i.mm"
include "eqtr4i.mm"

theorem rabiun
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B

  disjoint ph y
  disjoint A x
  disjoint x y
  assert |- { x e. U_ y e. A B | ph } = U_ y e. A { x e. B | ph }

  proof
    wph
    vx
    vy
    cA
    cB
    ciun
    #
    crab
    #
    vy
    cA
    vx
    cv
    #
    cB
    wcel
    #
    wph
    wa
    #
    vx
    cab
    #
    ciun
    #
    vy
    cA
    wph
    vx
    cB
    crab
    #
    ciun
    @2
    @0
    wcel
    #
    wph
    wa
    #
    vx
    cab
    @4
    vy
    cA
    wrex
    #
    vx
    cab
    @1
    @6
    @9
    @10
    vx
    @9
    @3
    vy
    cA
    wrex
    #
    wph
    wa
    @10
    @8
    @11
    wph
    vy
    @2
    cA
    cB
    eliun
    anbi1i
    @3
    wph
    vy
    cA
    r19.41v
    bitr4i
    abbii
    wph
    vx
    @0
    df-rab
    @4
    vy
    vx
    cA
    iunab
    3eqtr4i
    vy
    cA
    @7
    @5
    @7
    @5
    wceq
    vy
    cv
    cA
    wcel
    wph
    vx
    cB
    df-rab
    a1i
    iuneq2i
    eqtr4i
end
