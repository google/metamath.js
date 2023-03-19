include "wf1o.mm"
include "wf.mm"
include "wfn.mm"
include "f1of.mm"
include "ffn.mm"
include "syl.mm"

theorem f1ofn
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F : A -1-1-onto-> B -> F Fn A )

  proof
    cA
    cB
    cF
    wf1o
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
    f1of
    cA
    cB
    cF
    ffn
    syl
end
