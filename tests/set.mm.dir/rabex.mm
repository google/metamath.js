include "cvv.mm"
include "wcel.mm"
include "crab.mm"
include "rabexg.mm"
include "ax-mp.mm"

theorem rabex
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  assume rabex.1: |- A e. _V

  disjoint A x
  assert |- { x e. A | ph } e. _V

  proof
    cA
    cvv
    wcel
    wph
    vx
    cA
    crab
    cvv
    wcel
    rabex.1
    wph
    vx
    cA
    cvv
    rabexg
    ax-mp
end
