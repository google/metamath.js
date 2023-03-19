include "wceq.mm"
include "wss.mm"
include "wa.mm"
include "wb.mm"
include "eqss.mm"
include "wi.mm"
include "sstr2.mm"
include "adantl.mm"
include "adantr.mm"
include "impbid.mm"
include "sylbi.mm"

theorem sseq1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A = B -> ( A C_ C <-> B C_ C ) )

  proof
    cA
    cB
    wceq
    cA
    cB
    wss
    #
    cB
    cA
    wss
    #
    wa
    #
    cA
    cC
    wss
    #
    cB
    cC
    wss
    #
    wb
    cA
    cB
    eqss
    @2
    @3
    @4
    @1
    @3
    @4
    wi
    @0
    cB
    cA
    cC
    sstr2
    adantl
    @0
    @4
    @3
    wi
    @1
    cA
    cB
    cC
    sstr2
    adantr
    impbid
    sylbi
end
