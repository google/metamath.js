include "wfn.mm"
include "crn.mm"
include "wceq.mm"
include "wa.mm"
include "wss.mm"
include "wfo.mm"
include "wf.mm"
include "eqimss.mm"
include "anim2i.mm"
include "df-fo.mm"
include "df-f.mm"
include "3imtr4i.mm"

theorem fof
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F : A -onto-> B -> F : A --> B )

  proof
    cF
    cA
    wfn
    #
    cF
    crn
    #
    cB
    wceq
    #
    wa
    @0
    @1
    cB
    wss
    #
    wa
    cA
    cB
    cF
    wfo
    cA
    cB
    cF
    wf
    @2
    @3
    @0
    @1
    cB
    eqimss
    anim2i
    cA
    cB
    cF
    df-fo
    cA
    cB
    cF
    df-f
    3imtr4i
end
