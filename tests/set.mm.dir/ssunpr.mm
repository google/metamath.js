include "wss.mm"
include "cpr.mm"
include "cun.mm"
include "wa.mm"
include "csn.mm"
include "wo.mm"
include "wceq.mm"
include "df-pr.mm"
include "uneq2i.mm"
include "unass.mm"
include "eqtr4i.mm"
include "sseq2i.mm"
include "anbi2i.mm"
include "ssunsn2.mm"
include "ssunsn.mm"
include "un23.mm"
include "eqtr2i.mm"
include "eqeq2i.mm"
include "orbi2i.mm"
include "3bitri.mm"
include "orbi12i.mm"

theorem ssunpr
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( B C_ A /\ A C_ ( B u. { C , D } ) ) <-> ( ( A = B \/ A = ( B u. { C } ) ) \/ ( A = ( B u. { D } ) \/ A = ( B u. { C , D } ) ) ) )

  proof
    cB
    cA
    wss
    #
    cA
    cB
    cC
    cD
    cpr
    #
    cun
    #
    wss
    #
    wa
    @0
    cA
    cB
    cC
    csn
    #
    cun
    #
    cD
    csn
    #
    cun
    #
    wss
    #
    wa
    @0
    cA
    @5
    wss
    wa
    #
    cB
    @6
    cun
    #
    cA
    wss
    #
    @8
    wa
    #
    wo
    cA
    cB
    wceq
    cA
    @5
    wceq
    wo
    #
    cA
    @10
    wceq
    #
    cA
    @2
    wceq
    #
    wo
    #
    wo
    @3
    @8
    @0
    @2
    @7
    cA
    @2
    cB
    @4
    @6
    cun
    #
    cun
    @7
    @1
    @17
    cB
    cC
    cD
    df-pr
    uneq2i
    cB
    @4
    @6
    unass
    eqtr4i
    #
    sseq2i
    anbi2i
    cA
    cB
    @5
    cD
    ssunsn2
    @9
    @13
    @12
    @16
    cA
    cB
    cC
    ssunsn
    @12
    @11
    cA
    @10
    @4
    cun
    #
    wss
    #
    wa
    @14
    cA
    @19
    wceq
    #
    wo
    @16
    @8
    @20
    @11
    @7
    @19
    cA
    cB
    @4
    @6
    un23
    #
    sseq2i
    anbi2i
    cA
    @10
    cC
    ssunsn
    @21
    @15
    @14
    @19
    @2
    cA
    @2
    @7
    @19
    @18
    @22
    eqtr2i
    eqeq2i
    orbi2i
    3bitri
    orbi12i
    3bitri
end
