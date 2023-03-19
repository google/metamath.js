include "wceq.mm"
include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "wa.mm"
include "wf.mm"
include "sseq2.mm"
include "anbi2d.mm"
include "df-f.mm"
include "3bitr4g.mm"

theorem feq3
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F


  assert |- ( A = B -> ( F : C --> A <-> F : C --> B ) )

  proof
    cA
    cB
    wceq
    #
    cF
    cC
    wfn
    #
    cF
    crn
    #
    cA
    wss
    #
    wa
    @1
    @2
    cB
    wss
    #
    wa
    cC
    cA
    cF
    wf
    cC
    cB
    cF
    wf
    @0
    @3
    @4
    @1
    cA
    cB
    @2
    sseq2
    anbi2d
    cC
    cA
    cF
    df-f
    cC
    cB
    cF
    df-f
    3bitr4g
end
