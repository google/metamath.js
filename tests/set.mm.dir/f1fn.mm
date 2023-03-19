include "wf1.mm"
include "wf.mm"
include "wfn.mm"
include "f1f.mm"
include "ffn.mm"
include "syl.mm"

theorem f1fn
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F : A -1-1-> B -> F Fn A )

  proof
    cA
    cB
    cF
    wf1
    cA
    cB
    cF
    wf
    cF
    cA
    wfn
    cA
    cB
    cF
    f1f
    cA
    cB
    cF
    ffn
    syl
end
