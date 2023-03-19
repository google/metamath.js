include "wceq.mm"
include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "wa.mm"
include "wf.mm"
include "fneq2.mm"
include "anbi1d.mm"
include "df-f.mm"
include "3bitr4g.mm"

theorem feq2
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F


  assert |- ( A = B -> ( F : A --> C <-> F : B --> C ) )

  proof
    cA
    cB
    wceq
    #
    cF
    cA
    wfn
    #
    cF
    crn
    cC
    wss
    #
    wa
    cF
    cB
    wfn
    #
    @2
    wa
    cA
    cC
    cF
    wf
    cB
    cC
    cF
    wf
    @0
    @1
    @3
    @2
    cA
    cB
    cF
    fneq2
    anbi1d
    cA
    cC
    cF
    df-f
    cB
    cC
    cF
    df-f
    3bitr4g
end
