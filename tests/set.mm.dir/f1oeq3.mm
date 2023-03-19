include "wceq.mm"
include "wf1.mm"
include "wfo.mm"
include "wa.mm"
include "wf1o.mm"
include "f1eq3.mm"
include "foeq3.mm"
include "anbi12d.mm"
include "df-f1o.mm"
include "3bitr4g.mm"

theorem f1oeq3
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F


  assert |- ( A = B -> ( F : C -1-1-onto-> A <-> F : C -1-1-onto-> B ) )

  proof
    cA
    cB
    wceq
    #
    cC
    cA
    cF
    wf1
    #
    cC
    cA
    cF
    wfo
    #
    wa
    cC
    cB
    cF
    wf1
    #
    cC
    cB
    cF
    wfo
    #
    wa
    cC
    cA
    cF
    wf1o
    cC
    cB
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
    f1eq3
    cA
    cB
    cC
    cF
    foeq3
    anbi12d
    cC
    cA
    cF
    df-f1o
    cC
    cB
    cF
    df-f1o
    3bitr4g
end
