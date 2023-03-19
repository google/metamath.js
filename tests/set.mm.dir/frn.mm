include "wf.mm"
include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "df-f.mm"
include "simprbi.mm"

theorem frn
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F : A --> B -> ran F C_ B )

  proof
    cA
    cB
    cF
    wf
    cF
    cA
    wfn
    cF
    crn
    cB
    wss
    cA
    cB
    cF
    df-f
    simprbi
end
