include "wceq.mm"
include "wf1o.mm"
include "wb.mm"
include "f1oeq3.mm"
include "syl.mm"

theorem f1oeq3d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  assume f1oeq3d.1: |- ( ph -> A = B )


  assert |- ( ph -> ( F : C -1-1-onto-> A <-> F : C -1-1-onto-> B ) )

  proof
    wph
    cA
    cB
    wceq
    cC
    cA
    cF
    wf1o
    cC
    cB
    cF
    wf1o
    wb
    f1oeq3d.1
    cA
    cB
    cC
    cF
    f1oeq3
    syl
end
