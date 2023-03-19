include "wf1.mm"
include "wfn.mm"
include "wfun.mm"
include "f1fn.mm"
include "fnfun.mm"
include "syl.mm"

theorem f1fun
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F : A -1-1-> B -> Fun F )

  proof
    cA
    cB
    cF
    wf1
    cF
    cA
    wfn
    cF
    wfun
    cA
    cB
    cF
    f1fn
    cA
    cF
    fnfun
    syl
end
