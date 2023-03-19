include "cv.mm"
include "crab.mm"
include "cint.mm"
include "wcel.mm"
include "wi.mm"
include "wral.mm"
include "eleq1.mm"
include "wceq.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "vex.mm"
include "elintrab.mm"
include "vtoclbg.mm"

theorem elintrabg
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint ph y
  assert |- ( A e. V -> ( A e. |^| { x e. B | ph } <-> A. x e. B ( ph -> A e. x ) ) )

  proof
    vy
    cv
    #
    wph
    vx
    cB
    crab
    cint
    #
    wcel
    wph
    @0
    vx
    cv
    #
    wcel
    #
    wi
    #
    vx
    cB
    wral
    cA
    @1
    wcel
    wph
    cA
    @2
    wcel
    #
    wi
    #
    vx
    cB
    wral
    vy
    cA
    cV
    @0
    cA
    @1
    eleq1
    @0
    cA
    wceq
    #
    @4
    @6
    vx
    cB
    @7
    @3
    @5
    wph
    @0
    cA
    @2
    eleq1
    imbi2d
    ralbidv
    wph
    vx
    @0
    cB
    vy
    vex
    elintrab
    vtoclbg
end
