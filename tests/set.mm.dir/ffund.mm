include "wf.mm"
include "wfun.mm"
include "ffun.mm"
include "syl.mm"

theorem ffund
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  assume ffund.1: |- ( ph -> F : A --> B )


  assert |- ( ph -> Fun F )

  proof
    wph
    cA
    cB
    cF
    wf
    cF
    wfun
    ffund.1
    cA
    cB
    cF
    ffun
    syl
end
