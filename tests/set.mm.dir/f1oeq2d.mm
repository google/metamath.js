include "wceq.mm"
include "wf1o.mm"
include "wb.mm"
include "f1oeq2.mm"
include "syl.mm"

theorem f1oeq2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  assume f1oeq2d.1: |- ( ph -> A = B )


  assert |- ( ph -> ( F : A -1-1-onto-> C <-> F : B -1-1-onto-> C ) )

  proof
    wph
    cA
    cB
    wceq
    cA
    cC
    cF
    wf1o
    cB
    cC
    cF
    wf1o
    wb
    f1oeq2d.1
    cA
    cB
    cC
    cF
    f1oeq2
    syl
end
