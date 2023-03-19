include "wb.mm"
include "wral.mm"
include "wceq.mm"
include "crab.mm"
include "rabbi.mm"
include "biimpi.mm"
include "rabeqf.mm"
include "sylan9eqr.mm"

theorem rabeq12f
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume rabeq12f.1: |- F/_ x A
  assume rabeq12f.2: |- F/_ x B


  assert |- ( ( A = B /\ A. x e. A ( ph <-> ps ) ) -> { x e. A | ph } = { x e. B | ps } )

  proof
    wph
    wps
    wb
    vx
    cA
    wral
    #
    cA
    cB
    wceq
    wph
    vx
    cA
    crab
    #
    wps
    vx
    cA
    crab
    #
    wps
    vx
    cB
    crab
    @0
    @1
    @2
    wceq
    wph
    wps
    vx
    cA
    rabbi
    biimpi
    wps
    vx
    cA
    cB
    rabeq12f.1
    rabeq12f.2
    rabeqf
    sylan9eqr
end
