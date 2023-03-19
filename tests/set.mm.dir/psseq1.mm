include "wceq.mm"
include "wss.mm"
include "wne.mm"
include "wa.mm"
include "wpss.mm"
include "sseq1.mm"
include "neeq1.mm"
include "anbi12d.mm"
include "df-pss.mm"
include "3bitr4g.mm"

theorem psseq1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A = B -> ( A C. C <-> B C. C ) )

  proof
    cA
    cB
    wceq
    #
    cA
    cC
    wss
    #
    cA
    cC
    wne
    #
    wa
    cB
    cC
    wss
    #
    cB
    cC
    wne
    #
    wa
    cA
    cC
    wpss
    cB
    cC
    wpss
    @0
    @1
    @3
    @2
    @4
    cA
    cB
    cC
    sseq1
    cA
    cB
    cC
    neeq1
    anbi12d
    cA
    cC
    df-pss
    cB
    cC
    df-pss
    3bitr4g
end
