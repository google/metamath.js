include "cpr.mm"
include "wss.mm"
include "c0.mm"
include "cun.mm"
include "wa.mm"
include "wceq.mm"
include "csn.mm"
include "wo.mm"
include "uncom.mm"
include "un0.mm"
include "eqtri.mm"
include "sseq2i.mm"
include "0ss.mm"
include "biantrur.mm"
include "bitr3i.mm"
include "ssunpr.mm"
include "eqeq2i.mm"
include "orbi2i.mm"
include "orbi12i.mm"
include "3bitri.mm"

theorem sspr
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A C_ { B , C } <-> ( ( A = (/) \/ A = { B } ) \/ ( A = { C } \/ A = { B , C } ) ) )

  proof
    cA
    cB
    cC
    cpr
    #
    wss
    #
    c0
    cA
    wss
    #
    cA
    c0
    @0
    cun
    #
    wss
    #
    wa
    #
    cA
    c0
    wceq
    #
    cA
    c0
    cB
    csn
    #
    cun
    #
    wceq
    #
    wo
    #
    cA
    c0
    cC
    csn
    #
    cun
    #
    wceq
    #
    cA
    @3
    wceq
    #
    wo
    #
    wo
    @6
    cA
    @7
    wceq
    #
    wo
    #
    cA
    @11
    wceq
    #
    cA
    @0
    wceq
    #
    wo
    #
    wo
    @1
    @4
    @5
    @3
    @0
    cA
    @3
    @0
    c0
    cun
    @0
    c0
    @0
    uncom
    @0
    un0
    eqtri
    #
    sseq2i
    @2
    @4
    cA
    0ss
    biantrur
    bitr3i
    cA
    c0
    cB
    cC
    ssunpr
    @10
    @17
    @15
    @20
    @9
    @16
    @6
    @8
    @7
    cA
    @8
    @7
    c0
    cun
    @7
    c0
    @7
    uncom
    @7
    un0
    eqtri
    eqeq2i
    orbi2i
    @13
    @18
    @14
    @19
    @12
    @11
    cA
    @12
    @11
    c0
    cun
    @11
    c0
    @11
    uncom
    @11
    un0
    eqtri
    eqeq2i
    @3
    @0
    cA
    @21
    eqeq2i
    orbi12i
    orbi12i
    3bitri
end
