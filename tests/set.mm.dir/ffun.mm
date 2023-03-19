include "wf.mm"
include "wfn.mm"
include "wfun.mm"
include "ffn.mm"
include "fnfun.mm"
include "syl.mm"

theorem ffun
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F : A --> B -> Fun F )

  proof
    cA
    cB
    cF
    wf
    cF
    cA
    wfn
    cF
    wfun
    cA
    cB
    cF
    ffn
    cA
    cF
    fnfun
    syl
end
