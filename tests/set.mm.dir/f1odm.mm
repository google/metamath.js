include "wf1o.mm"
include "wfn.mm"
include "cdm.mm"
include "wceq.mm"
include "f1ofn.mm"
include "fndm.mm"
include "syl.mm"

theorem f1odm
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F : A -1-1-onto-> B -> dom F = A )

  proof
    cA
    cB
    cF
    wf1o
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
    f1ofn
    cA
    cF
    fndm
    syl
end
