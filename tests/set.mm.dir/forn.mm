include "wfo.mm"
include "wfn.mm"
include "crn.mm"
include "wceq.mm"
include "df-fo.mm"
include "simprbi.mm"

theorem forn
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F : A -onto-> B -> ran F = B )

  proof
    cA
    cB
    cF
    wfo
    cF
    cA
    wfn
    cF
    crn
    cB
    wceq
    cA
    cB
    cF
    df-fo
    simprbi
end
