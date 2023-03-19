include "wceq.mm"
include "crab.mm"
include "rabeq.mm"
include "syl.mm"

theorem rabeqd
  let wph: wff ph
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume rabeqd.1: |- ( ph -> A = B )

  disjoint A x
  disjoint B x
  assert |- ( ph -> { x e. A | ch } = { x e. B | ch } )

  proof
    wph
    cA
    cB
    wceq
    wch
    vx
    cA
    crab
    wch
    vx
    cB
    crab
    wceq
    rabeqd.1
    wch
    vx
    cA
    cB
    rabeq
    syl
end
