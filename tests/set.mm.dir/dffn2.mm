include "wfn.mm"
include "crn.mm"
include "cvv.mm"
include "wss.mm"
include "wa.mm"
include "wf.mm"
include "ssv.mm"
include "biantru.mm"
include "df-f.mm"
include "bitr4i.mm"

theorem dffn2
  let cA: class A
  let cF: class F


  assert |- ( F Fn A <-> F : A --> _V )

  proof
    cF
    cA
    wfn
    #
    @0
    cF
    crn
    #
    cvv
    wss
    #
    wa
    cA
    cvv
    cF
    wf
    @2
    @0
    @1
    ssv
    biantru
    cA
    cvv
    cF
    df-f
    bitr4i
end
