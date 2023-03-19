include "wfn.mm"
include "wfun.mm"
include "cdm.mm"
include "wceq.mm"
include "df-fn.mm"
include "simprbi.mm"

theorem fndm
  let cA: class A
  let cF: class F


  assert |- ( F Fn A -> dom F = A )

  proof
    cF
    cA
    wfn
    cF
    wfun
    cF
    cdm
    cA
    wceq
    cF
    cA
    df-fn
    simprbi
end
