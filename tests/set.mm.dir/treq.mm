include "wceq.mm"
include "cuni.mm"
include "wss.mm"
include "wtr.mm"
include "unieq.mm"
include "sseq1d.mm"
include "sseq2.mm"
include "bitrd.mm"
include "df-tr.mm"
include "3bitr4g.mm"

theorem treq
  let cA: class A
  let cB: class B


  assert |- ( A = B -> ( Tr A <-> Tr B ) )

  proof
    cA
    cB
    wceq
    #
    cA
    cuni
    #
    cA
    wss
    #
    cB
    cuni
    #
    cB
    wss
    #
    cA
    wtr
    cB
    wtr
    @0
    @2
    @3
    cA
    wss
    @4
    @0
    @1
    @3
    cA
    cA
    cB
    unieq
    sseq1d
    cA
    cB
    @3
    sseq2
    bitrd
    cA
    df-tr
    cB
    df-tr
    3bitr4g
end
