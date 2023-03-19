include "wf1o.mm"
include "wfo.mm"
include "ccnv.mm"
include "wfun.mm"
include "dff1o3.mm"
include "simplbi.mm"

theorem f1ofo
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F : A -1-1-onto-> B -> F : A -onto-> B )

  proof
    cA
    cB
    cF
    wf1o
    cA
    cB
    cF
    wfo
    cF
    ccnv
    wfun
    cA
    cB
    cF
    dff1o3
    simplbi
end
