include "wf1o.mm"
include "wf1.mm"
include "wfo.mm"
include "df-f1o.mm"
include "simplbi.mm"

theorem f1of1
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F : A -1-1-onto-> B -> F : A -1-1-> B )

  proof
    cA
    cB
    cF
    wf1o
    cA
    cB
    cF
    wf1
    cA
    cB
    cF
    wfo
    cA
    cB
    cF
    df-f1o
    simplbi
end
