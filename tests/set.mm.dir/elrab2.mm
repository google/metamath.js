include "wcel.mm"
include "crab.mm"
include "wa.mm"
include "eleq2i.mm"
include "elrab.mm"
include "bitri.mm"

theorem elrab2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume elrab2.1: |- ( x = A -> ( ph <-> ps ) )
  assume elrab2.2: |- C = { x e. B | ph }

  disjoint ps x
  disjoint A x
  disjoint B x
  assert |- ( A e. C <-> ( A e. B /\ ps ) )

  proof
    cA
    cC
    wcel
    cA
    wph
    vx
    cB
    crab
    #
    wcel
    cA
    cB
    wcel
    wps
    wa
    cC
    @0
    cA
    elrab2.2
    eleq2i
    wph
    wps
    vx
    cA
    cB
    elrab2.1
    elrab
    bitri
end
