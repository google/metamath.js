include "wceq.mm"
include "wfn.mm"
include "crn.mm"
include "wa.mm"
include "wfo.mm"
include "fneq2.mm"
include "anbi1d.mm"
include "df-fo.mm"
include "3bitr4g.mm"

theorem foeq2
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F


  assert |- ( A = B -> ( F : A -onto-> C <-> F : B -onto-> C ) )

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
    wceq
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
    wfo
    cB
    cC
    cF
    wfo
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
    df-fo
    cB
    cC
    cF
    df-fo
    3bitr4g
end
