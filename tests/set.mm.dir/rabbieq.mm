include "crab.mm"
include "rabbii.mm"
include "eqtri.mm"

theorem rabbieq
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume rabbieq.1: |- B = { x e. A | ph }
  assume rabbieq.2: |- ( ph <-> ps )


  assert |- B = { x e. A | ps }

  proof
    cB
    wph
    vx
    cA
    crab
    wps
    vx
    cA
    crab
    rabbieq.1
    wph
    wps
    vx
    cA
    rabbieq.2
    rabbii
    eqtri
end
