include "wss.mm"
include "wf.mm"
include "wfn.mm"
include "crn.mm"
include "wa.mm"
include "sstr2.mm"
include "com12.mm"
include "anim2d.mm"
include "df-f.mm"
include "3imtr4g.mm"
include "impcom.mm"

theorem fss
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F


  assert |- ( ( F : A --> B /\ B C_ C ) -> F : A --> C )

  proof
    cB
    cC
    wss
    #
    cA
    cB
    cF
    wf
    #
    cA
    cC
    cF
    wf
    #
    @0
    cF
    cA
    wfn
    #
    cF
    crn
    #
    cB
    wss
    #
    wa
    @3
    @4
    cC
    wss
    #
    wa
    @1
    @2
    @0
    @5
    @6
    @3
    @5
    @0
    @6
    @4
    cB
    cC
    sstr2
    com12
    anim2d
    cA
    cB
    cF
    df-f
    cA
    cC
    cF
    df-f
    3imtr4g
    impcom
end
