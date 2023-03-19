include "nfv.mm"
include "rspc.mm"

theorem rspcv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume rspcv.1: |- ( x = A -> ( ph <-> ps ) )

  disjoint A x
  disjoint B x
  disjoint ps x
  assert |- ( A e. B -> ( A. x e. B ph -> ps ) )

  proof
    wph
    wps
    vx
    cA
    cB
    wps
    vx
    nfv
    rspcv.1
    rspc
end
