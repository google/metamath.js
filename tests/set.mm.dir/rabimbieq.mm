include "crab.mm"
include "rabbiia.mm"
include "eqtri.mm"

theorem rabimbieq
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume rabimbieq.1: |- B = { x e. A | ph }
  assume rabimbieq.2: |- ( x e. A -> ( ph <-> ps ) )


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
    rabimbieq.1
    wph
    wps
    vx
    cA
    rabimbieq.2
    rabbiia
    eqtri
end
