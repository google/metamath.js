include "wcel.mm"
include "wa.mm"
include "crab.mm"
include "cint.mm"
include "wss.mm"
include "elrab.mm"
include "intss1.mm"
include "sylbir.mm"

theorem intminss
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume intminss.1: |- ( x = A -> ( ph <-> ps ) )

  disjoint A x
  disjoint B x
  disjoint ps x
  assert |- ( ( A e. B /\ ps ) -> |^| { x e. B | ph } C_ A )

  proof
    cA
    cB
    wcel
    wps
    wa
    cA
    wph
    vx
    cB
    crab
    #
    wcel
    @0
    cint
    cA
    wss
    wph
    wps
    vx
    cA
    cB
    intminss.1
    elrab
    cA
    @0
    intss1
    sylbir
end
