include "wf1o.mm"
include "wfn.mm"
include "wfun.mm"
include "f1ofn.mm"
include "fnfun.mm"
include "syl.mm"

theorem f1ofun
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F : A -1-1-onto-> B -> Fun F )

  proof
    cA
    cB
    cF
    wf1o
    cF
    cA
    wfn
    cF
    wfun
    cA
    cB
    cF
    f1ofn
    cA
    cF
    fnfun
    syl
end
