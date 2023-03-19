include "wceq.mm"
include "wf1.mm"
include "wfo.mm"
include "wa.mm"
include "wf1o.mm"
include "f1eq2.mm"
include "foeq2.mm"
include "anbi12d.mm"
include "df-f1o.mm"
include "3bitr4g.mm"

theorem f1oeq2
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F


  assert |- ( A = B -> ( F : A -1-1-onto-> C <-> F : B -1-1-onto-> C ) )

  proof
    cA
    cB
    wceq
    #
    cA
    cC
    cF
    wf1
    #
    cA
    cC
    cF
    wfo
    #
    wa
    cB
    cC
    cF
    wf1
    #
    cB
    cC
    cF
    wfo
    #
    wa
    cA
    cC
    cF
    wf1o
    cB
    cC
    cF
    wf1o
    @0
    @1
    @3
    @2
    @4
    cA
    cB
    cC
    cF
    f1eq2
    cA
    cB
    cC
    cF
    foeq2
    anbi12d
    cA
    cC
    cF
    df-f1o
    cB
    cC
    cF
    df-f1o
    3bitr4g
end
