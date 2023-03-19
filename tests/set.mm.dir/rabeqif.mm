include "wceq.mm"
include "crab.mm"
include "rabeqf.mm"
include "ax-mp.mm"

theorem rabeqif
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume rabeqf.1: |- F/_ x A
  assume rabeqf.2: |- F/_ x B
  assume rabeqif.3: |- A = B


  assert |- { x e. A | ph } = { x e. B | ph }

  proof
    cA
    cB
    wceq
    wph
    vx
    cA
    crab
    wph
    vx
    cB
    crab
    wceq
    rabeqif.3
    wph
    vx
    cA
    cB
    rabeqf.1
    rabeqf.2
    rabeqf
    ax-mp
end
