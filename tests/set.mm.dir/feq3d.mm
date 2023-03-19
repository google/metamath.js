include "wceq.mm"
include "wf.mm"
include "wb.mm"
include "feq3.mm"
include "syl.mm"

theorem feq3d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cX: class X
  assume feq2d.1: |- ( ph -> A = B )


  assert |- ( ph -> ( F : X --> A <-> F : X --> B ) )

  proof
    wph
    cA
    cB
    wceq
    cX
    cA
    cF
    wf
    cX
    cB
    cF
    wf
    wb
    feq2d.1
    cA
    cB
    cX
    cF
    feq3
    syl
end
