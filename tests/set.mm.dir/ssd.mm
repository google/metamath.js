include "nfv.mm"
include "ssdf.mm"

theorem ssd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume ssd.1: |- ( ( ph /\ x e. A ) -> x e. B )

  disjoint A x
  disjoint B x
  disjoint ph x
  assert |- ( ph -> A C_ B )

  proof
    wph
    vx
    cA
    cB
    wph
    vx
    nfv
    ssd.1
    ssdf
end
