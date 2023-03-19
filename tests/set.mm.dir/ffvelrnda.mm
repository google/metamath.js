include "wf.mm"
include "wcel.mm"
include "cfv.mm"
include "ffvelrn.mm"
include "sylan.mm"

theorem ffvelrnda
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  assume ffvelrnd.1: |- ( ph -> F : A --> B )


  assert |- ( ( ph /\ C e. A ) -> ( F ` C ) e. B )

  proof
    wph
    cA
    cB
    cF
    wf
    cC
    cA
    wcel
    cC
    cF
    cfv
    cB
    wcel
    ffvelrnd.1
    cA
    cB
    cC
    cF
    ffvelrn
    sylan
end
