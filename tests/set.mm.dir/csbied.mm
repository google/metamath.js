include "nfv.mm"
include "nfcvd.mm"
include "csbiedf.mm"

theorem csbied
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  assume csbied.1: |- ( ph -> A e. V )
  assume csbied.2: |- ( ( ph /\ x = A ) -> B = C )

  disjoint A x
  disjoint C x
  disjoint ph x
  assert |- ( ph -> [_ A / x ]_ B = C )

  proof
    wph
    vx
    cA
    cB
    cC
    cV
    wph
    vx
    nfv
    wph
    vx
    cC
    nfcvd
    csbied.1
    csbied.2
    csbiedf
end
