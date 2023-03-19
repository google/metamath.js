include "nfv.mm"
include "elintd.mm"

theorem elintdv
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  assume elintdv.1: |- ( ph -> A e. V )
  assume elintdv.2: |- ( ( ph /\ x e. B ) -> A e. x )

  disjoint A x
  disjoint B x
  disjoint ph x
  assert |- ( ph -> A e. |^| B )

  proof
    wph
    vx
    cA
    cB
    cV
    wph
    vx
    nfv
    elintdv.1
    elintdv.2
    elintd
end
