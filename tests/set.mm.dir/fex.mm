include "wf.mm"
include "wfn.mm"
include "wcel.mm"
include "cvv.mm"
include "ffn.mm"
include "fnex.mm"
include "sylan.mm"

theorem fex
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F


  assert |- ( ( F : A --> B /\ A e. C ) -> F e. _V )

  proof
    cA
    cB
    cF
    wf
    cF
    cA
    wfn
    cA
    cC
    wcel
    cF
    cvv
    wcel
    cA
    cB
    cF
    ffn
    cA
    cC
    cF
    fnex
    sylan
end
