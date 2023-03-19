include "wceq.mm"
include "wf.mm"
include "wb.mm"
include "feq1.mm"
include "syl.mm"

theorem feq1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  assume feq1d.1: |- ( ph -> F = G )


  assert |- ( ph -> ( F : A --> B <-> G : A --> B ) )

  proof
    wph
    cF
    cG
    wceq
    cA
    cB
    cF
    wf
    cA
    cB
    cG
    wf
    wb
    feq1d.1
    cA
    cB
    cF
    cG
    feq1
    syl
end
