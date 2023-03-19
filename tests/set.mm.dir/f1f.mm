include "wf1.mm"
include "wf.mm"
include "ccnv.mm"
include "wfun.mm"
include "df-f1.mm"
include "simplbi.mm"

theorem f1f
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F : A -1-1-> B -> F : A --> B )

  proof
    cA
    cB
    cF
    wf1
    cA
    cB
    cF
    wf
    cF
    ccnv
    wfun
    cA
    cB
    cF
    df-f1
    simplbi
end
