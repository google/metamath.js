include "wceq.mm"
include "wf1.mm"
include "wfo.mm"
include "wa.mm"
include "wf1o.mm"
include "f1eq1.mm"
include "foeq1.mm"
include "anbi12d.mm"
include "df-f1o.mm"
include "3bitr4g.mm"

theorem f1oeq1
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G


  assert |- ( F = G -> ( F : A -1-1-onto-> B <-> G : A -1-1-onto-> B ) )

  proof
    cF
    cG
    wceq
    #
    cA
    cB
    cF
    wf1
    #
    cA
    cB
    cF
    wfo
    #
    wa
    cA
    cB
    cG
    wf1
    #
    cA
    cB
    cG
    wfo
    #
    wa
    cA
    cB
    cF
    wf1o
    cA
    cB
    cG
    wf1o
    @0
    @1
    @3
    @2
    @4
    cA
    cB
    cF
    cG
    f1eq1
    cA
    cB
    cF
    cG
    foeq1
    anbi12d
    cA
    cB
    cF
    df-f1o
    cA
    cB
    cG
    df-f1o
    3bitr4g
end
