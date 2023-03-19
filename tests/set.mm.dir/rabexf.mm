include "wcel.mm"
include "crab.mm"
include "cvv.mm"
include "rabexgf.mm"
include "ax-mp.mm"

theorem rabexf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume rabexf.1: |- F/_ x A
  assume rabexf.2: |- A e. V


  assert |- { x e. A | ph } e. _V

  proof
    cA
    cV
    wcel
    wph
    vx
    cA
    crab
    cvv
    wcel
    rabexf.2
    wph
    vx
    cA
    cV
    rabexf.1
    rabexgf
    ax-mp
end
