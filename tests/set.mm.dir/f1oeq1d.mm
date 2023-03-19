include "wceq.mm"
include "wf1o.mm"
include "wb.mm"
include "f1oeq1.mm"
include "syl.mm"

theorem f1oeq1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  assume f1oeq1d.1: |- ( ph -> F = G )


  assert |- ( ph -> ( F : A -1-1-onto-> B <-> G : A -1-1-onto-> B ) )

  proof
    wph
    cF
    cG
    wceq
    cA
    cB
    cF
    wf1o
    cA
    cB
    cG
    wf1o
    wb
    f1oeq1d.1
    cA
    cB
    cF
    cG
    f1oeq1
    syl
end
