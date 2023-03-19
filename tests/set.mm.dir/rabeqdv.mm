include "wceq.mm"
include "crab.mm"
include "rabeq.mm"
include "syl.mm"

theorem rabeqdv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume rabeqdv.1: |- ( ph -> A = B )

  disjoint A x
  disjoint B x
  disjoint ph x
  assert |- ( ph -> { x e. A | ps } = { x e. B | ps } )

  proof
    wph
    cA
    cB
    wceq
    wps
    vx
    cA
    crab
    wps
    vx
    cB
    crab
    wceq
    rabeqdv.1
    wps
    vx
    cA
    cB
    rabeq
    syl
end
