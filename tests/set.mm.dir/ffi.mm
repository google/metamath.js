include "wf.mm"
include "wfn.mm"
include "cfn.mm"
include "wcel.mm"
include "ffn.mm"
include "fnfi.mm"
include "sylan.mm"

theorem ffi
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( ( F : A --> B /\ A e. Fin ) -> F e. Fin )

  proof
    cA
    cB
    cF
    wf
    cF
    cA
    wfn
    cA
    cfn
    wcel
    cF
    cfn
    wcel
    cA
    cB
    cF
    ffn
    cA
    cF
    fnfi
    sylan
end
