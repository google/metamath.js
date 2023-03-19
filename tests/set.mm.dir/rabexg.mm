include "crab.mm"
include "wss.mm"
include "wcel.mm"
include "cvv.mm"
include "ssrab2.mm"
include "ssexg.mm"
include "mpan.mm"

theorem rabexg
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cV: class V

  disjoint A x
  assert |- ( A e. V -> { x e. A | ph } e. _V )

  proof
    wph
    vx
    cA
    crab
    #
    cA
    wss
    cA
    cV
    wcel
    @0
    cvv
    wcel
    wph
    vx
    cA
    ssrab2
    @0
    cA
    cV
    ssexg
    mpan
end
