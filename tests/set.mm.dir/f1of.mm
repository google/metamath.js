include "wf1o.mm"
include "wf1.mm"
include "wf.mm"
include "f1of1.mm"
include "f1f.mm"
include "syl.mm"

theorem f1of
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F : A -1-1-onto-> B -> F : A --> B )

  proof
    cA
    cB
    cF
    wf1o
    cA
    cB
    cF
    wf1
    cA
    cB
    cF
    wf
    cA
    cB
    cF
    f1of1
    cA
    cB
    cF
    f1f
    syl
end
