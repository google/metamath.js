include "wf1.mm"
include "wfn.mm"
include "cdm.mm"
include "wceq.mm"
include "f1fn.mm"
include "fndm.mm"
include "syl.mm"

theorem f1dm
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F : A -1-1-> B -> dom F = A )

  proof
    cA
    cB
    cF
    wf1
    cF
    cA
    wfn
    cF
    cdm
    cA
    wceq
    cA
    cB
    cF
    f1fn
    cA
    cF
    fndm
    syl
end
