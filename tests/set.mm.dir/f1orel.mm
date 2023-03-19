include "wf1o.mm"
include "wfun.mm"
include "wrel.mm"
include "f1ofun.mm"
include "funrel.mm"
include "syl.mm"

theorem f1orel
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F : A -1-1-onto-> B -> Rel F )

  proof
    cA
    cB
    cF
    wf1o
    cF
    wfun
    cF
    wrel
    cA
    cB
    cF
    f1ofun
    cF
    funrel
    syl
end
