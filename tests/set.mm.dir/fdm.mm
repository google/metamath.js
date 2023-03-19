include "wf.mm"
include "wfn.mm"
include "cdm.mm"
include "wceq.mm"
include "ffn.mm"
include "fndm.mm"
include "syl.mm"

theorem fdm
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F : A --> B -> dom F = A )

  proof
    cA
    cB
    cF
    wf
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
    ffn
    cA
    cF
    fndm
    syl
end
