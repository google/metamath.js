include "wceq.mm"
include "wss.mm"
include "wne.mm"
include "wa.mm"
include "wpss.mm"
include "sseq2.mm"
include "neeq2.mm"
include "anbi12d.mm"
include "df-pss.mm"
include "3bitr4g.mm"

theorem psseq2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A = B -> ( C C. A <-> C C. B ) )

  proof
    cA
    cB
    wceq
    #
    cC
    cA
    wss
    #
    cC
    cA
    wne
    #
    wa
    cC
    cB
    wss
    #
    cC
    cB
    wne
    #
    wa
    cC
    cA
    wpss
    cC
    cB
    wpss
    @0
    @1
    @3
    @2
    @4
    cA
    cB
    cC
    sseq2
    cA
    cB
    cC
    neeq2
    anbi12d
    cC
    cA
    df-pss
    cC
    cB
    df-pss
    3bitr4g
end
