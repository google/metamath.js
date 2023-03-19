include "wf.mm"
include "wfn.mm"
include "wrel.mm"
include "ffn.mm"
include "fnrel.mm"
include "syl.mm"

theorem frel
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F : A --> B -> Rel F )

  proof
    cA
    cB
    cF
    wf
    cF
    cA
    wfn
    cF
    wrel
    cA
    cB
    cF
    ffn
    cA
    cF
    fnrel
    syl
end
