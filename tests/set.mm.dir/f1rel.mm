include "wf1.mm"
include "wfn.mm"
include "wrel.mm"
include "f1fn.mm"
include "fnrel.mm"
include "syl.mm"

theorem f1rel
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F : A -1-1-> B -> Rel F )

  proof
    cA
    cB
    cF
    wf1
    cF
    cA
    wfn
    cF
    wrel
    cA
    cB
    cF
    f1fn
    cA
    cF
    fnrel
    syl
end
