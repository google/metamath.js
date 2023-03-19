include "crab.mm"
include "wcel.mm"
include "elrab.mm"
include "baib.mm"

theorem elrab3
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume elrab.1: |- ( x = A -> ( ph <-> ps ) )

  disjoint ps x
  disjoint A x
  disjoint B x
  assert |- ( A e. B -> ( A e. { x e. B | ph } <-> ps ) )

  proof
    cA
    wph
    vx
    cB
    crab
    wcel
    cA
    cB
    wcel
    wps
    wph
    wps
    vx
    cA
    cB
    elrab.1
    elrab
    baib
end
