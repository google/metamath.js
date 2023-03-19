include "wf.mm"
include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "crn.mm"
include "ffi.mm"
include "rnfi.mm"
include "syl.mm"

theorem rnffi
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( ( F : A --> B /\ A e. Fin ) -> ran F e. Fin )

  proof
    cA
    cB
    cF
    wf
    cA
    cfn
    wcel
    wa
    cF
    cfn
    wcel
    cF
    crn
    cfn
    wcel
    cA
    cB
    cF
    ffi
    cF
    rnfi
    syl
end
