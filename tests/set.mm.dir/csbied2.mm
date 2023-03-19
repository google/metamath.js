include "cv.mm"
include "wceq.mm"
include "id.mm"
include "sylan9eqr.mm"
include "syldan.mm"
include "csbied.mm"

theorem csbied2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V
  assume csbied2.1: |- ( ph -> A e. V )
  assume csbied2.2: |- ( ph -> A = B )
  assume csbied2.3: |- ( ( ph /\ x = B ) -> C = D )

  disjoint A x
  disjoint ph x
  disjoint D x
  assert |- ( ph -> [_ A / x ]_ C = D )

  proof
    wph
    vx
    cA
    cC
    cD
    cV
    csbied2.1
    wph
    vx
    cv
    #
    cA
    wceq
    #
    @0
    cB
    wceq
    cC
    cD
    wceq
    @1
    wph
    @0
    cA
    cB
    @1
    id
    csbied2.2
    sylan9eqr
    csbied2.3
    syldan
    csbied
end
