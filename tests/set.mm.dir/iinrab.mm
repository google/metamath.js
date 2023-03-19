include "c0.mm"
include "wne.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wral.mm"
include "cab.mm"
include "crab.mm"
include "ciin.mm"
include "r19.28zv.mm"
include "abbidv.mm"
include "wceq.mm"
include "df-rab.mm"
include "a1i.mm"
include "iineq2i.mm"
include "iinab.mm"
include "eqtri.mm"
include "3eqtr4g.mm"

theorem iinrab
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B

  disjoint A y
  disjoint x y
  disjoint A x
  disjoint B x
  assert |- ( A =/= (/) -> |^|_ x e. A { y e. B | ph } = { y e. B | A. x e. A ph } )

  proof
    cA
    c0
    wne
    #
    vy
    cv
    cB
    wcel
    #
    wph
    wa
    #
    vx
    cA
    wral
    #
    vy
    cab
    #
    @1
    wph
    vx
    cA
    wral
    #
    wa
    #
    vy
    cab
    vx
    cA
    wph
    vy
    cB
    crab
    #
    ciin
    #
    @5
    vy
    cB
    crab
    @0
    @3
    @6
    vy
    @1
    wph
    vx
    cA
    r19.28zv
    abbidv
    @8
    vx
    cA
    @2
    vy
    cab
    #
    ciin
    @4
    vx
    cA
    @7
    @9
    @7
    @9
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
    iineq2i
    @2
    vx
    vy
    cA
    iinab
    eqtri
    @5
    vy
    cB
    df-rab
    3eqtr4g
end
