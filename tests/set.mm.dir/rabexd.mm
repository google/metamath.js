include "crab.mm"
include "cvv.mm"
include "wcel.mm"
include "rabexg.mm"
include "syl.mm"
include "syl5eqel.mm"

theorem rabexd
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  assume rabexd.1: |- B = { x e. A | ps }
  assume rabexd.2: |- ( ph -> A e. V )

  disjoint A x
  assert |- ( ph -> B e. _V )

  proof
    wph
    cB
    wps
    vx
    cA
    crab
    #
    cvv
    rabexd.1
    wph
    cA
    cV
    wcel
    @0
    cvv
    wcel
    rabexd.2
    wps
    vx
    cA
    cV
    rabexg
    syl
    syl5eqel
end
