include "wcel.mm"
include "wral.mm"
include "crn.mm"
include "wss.mm"
include "cv.mm"
include "ex.mm"
include "ralrimi.mm"
include "rnmptss.mm"
include "syl.mm"

theorem rnmptssd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  assume rnmptssd.1: |- F/ x ph
  assume rnmptssd.2: |- F = ( x e. A |-> B )
  assume rnmptssd.3: |- ( ( ph /\ x e. A ) -> B e. C )

  disjoint A x
  disjoint C x
  assert |- ( ph -> ran F C_ C )

  proof
    wph
    cB
    cC
    wcel
    #
    vx
    cA
    wral
    cF
    crn
    cC
    wss
    wph
    @0
    vx
    cA
    rnmptssd.1
    wph
    vx
    cv
    cA
    wcel
    @0
    rnmptssd.3
    ex
    ralrimi
    vx
    cA
    cB
    cC
    cF
    rnmptssd.2
    rnmptss
    syl
end
