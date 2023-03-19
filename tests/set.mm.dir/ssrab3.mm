include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"

theorem ssrab3
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume ssrab3.1: |- B = { x e. A | ph }

  disjoint A x
  assert |- B C_ A

  proof
    cB
    wph
    vx
    cA
    crab
    cA
    ssrab3.1
    wph
    vx
    cA
    ssrab2
    eqsstri
end
