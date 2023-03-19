include "wcel.mm"
include "wral.mm"
include "rspcv.mm"
include "imp.mm"

theorem rspcva
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume rspcv.1: |- ( x = A -> ( ph <-> ps ) )

  disjoint A x
  disjoint B x
  disjoint ps x
  assert |- ( ( A e. B /\ A. x e. B ph ) -> ps )

  proof
    cA
    cB
    wcel
    wph
    vx
    cB
    wral
    wps
    wph
    wps
    vx
    cA
    cB
    rspcv.1
    rspcv
    imp
end
