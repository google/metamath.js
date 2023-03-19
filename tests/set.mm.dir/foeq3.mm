include "wceq.mm"
include "wfn.mm"
include "crn.mm"
include "wa.mm"
include "wfo.mm"
include "eqeq2.mm"
include "anbi2d.mm"
include "df-fo.mm"
include "3bitr4g.mm"

theorem foeq3
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F


  assert |- ( A = B -> ( F : C -onto-> A <-> F : C -onto-> B ) )

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
    wceq
    #
    wa
    @1
    @2
    cB
    wceq
    #
    wa
    cC
    cA
    cF
    wfo
    cC
    cB
    cF
    wfo
    @0
    @3
    @4
    @1
    cA
    cB
    @2
    eqeq2
    anbi2d
    cC
    cA
    cF
    df-fo
    cC
    cB
    cF
    df-fo
    3bitr4g
end
