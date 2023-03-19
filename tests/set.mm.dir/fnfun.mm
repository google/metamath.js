include "wfn.mm"
include "wfun.mm"
include "cdm.mm"
include "wceq.mm"
include "df-fn.mm"
include "simplbi.mm"

theorem fnfun
  let cA: class A
  let cF: class F


  assert |- ( F Fn A -> Fun F )

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
    simplbi
end
