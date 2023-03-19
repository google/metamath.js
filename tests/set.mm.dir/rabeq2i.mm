include "cv.mm"
include "wcel.mm"
include "crab.mm"
include "wa.mm"
include "eleq2i.mm"
include "rabid.mm"
include "bitri.mm"

theorem rabeq2i
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume rabeq2i.1: |- A = { x e. B | ph }


  assert |- ( x e. A <-> ( x e. B /\ ph ) )

  proof
    vx
    cv
    #
    cA
    wcel
    @0
    wph
    vx
    cB
    crab
    #
    wcel
    @0
    cB
    wcel
    wph
    wa
    cA
    @1
    @0
    rabeq2i.1
    eleq2i
    wph
    vx
    cB
    rabid
    bitri
end
