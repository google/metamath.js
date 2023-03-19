include "wf.mm"
include "wcel.mm"
include "cfv.mm"
include "ffvelrn.mm"
include "mpan.mm"

theorem ffvelrni
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  assume ffvrni.1: |- F : A --> B


  assert |- ( C e. A -> ( F ` C ) e. B )

  proof
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
    ffvrni.1
    cA
    cB
    cC
    cF
    ffvelrn
    mpan
end
