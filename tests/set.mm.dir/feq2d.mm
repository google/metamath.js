include "wceq.mm"
include "wf.mm"
include "wb.mm"
include "feq2.mm"
include "syl.mm"

theorem feq2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  assume feq2d.1: |- ( ph -> A = B )


  assert |- ( ph -> ( F : A --> C <-> F : B --> C ) )

  proof
    wph
    cA
    cB
    wceq
    cA
    cC
    cF
    wf
    cB
    cC
    cF
    wf
    wb
    feq2d.1
    cA
    cB
    cC
    cF
    feq2
    syl
end
