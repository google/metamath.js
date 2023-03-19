include "ctp.mm"
include "wss.mm"
include "cpr.mm"
include "csn.mm"
include "cun.mm"
include "c0.mm"
include "wa.mm"
include "wceq.mm"
include "wo.mm"
include "df-tp.mm"
include "sseq2i.mm"
include "0ss.mm"
include "biantrur.mm"
include "ssunsn2.mm"
include "sspr.mm"
include "bitr3i.mm"
include "uncom.mm"
include "un0.mm"
include "eqtri.mm"
include "sseq1i.mm"
include "anbi12i.mm"
include "ssunpr.mm"
include "df-pr.mm"
include "eqtr4i.mm"
include "eqeq2i.mm"
include "orbi2i.mm"
include "eqtr2i.mm"
include "orbi12i.mm"
include "3bitri.mm"
include "bitri.mm"

theorem sstp
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( A C_ { B , C , D } <-> ( ( ( A = (/) \/ A = { B } ) \/ ( A = { C } \/ A = { B , C } ) ) \/ ( ( A = { D } \/ A = { B , D } ) \/ ( A = { C , D } \/ A = { B , C , D } ) ) ) )

  proof
    cA
    cB
    cC
    cD
    ctp
    #
    wss
    cA
    cB
    cC
    cpr
    #
    cD
    csn
    #
    cun
    #
    wss
    #
    c0
    cA
    wss
    #
    @4
    wa
    #
    cA
    c0
    wceq
    cA
    cB
    csn
    #
    wceq
    wo
    cA
    cC
    csn
    #
    wceq
    cA
    @1
    wceq
    wo
    wo
    #
    cA
    @2
    wceq
    #
    cA
    cB
    cD
    cpr
    #
    wceq
    #
    wo
    #
    cA
    cC
    cD
    cpr
    #
    wceq
    #
    cA
    @0
    wceq
    #
    wo
    #
    wo
    #
    wo
    #
    @0
    @3
    cA
    cB
    cC
    cD
    df-tp
    #
    sseq2i
    @5
    @4
    cA
    0ss
    #
    biantrur
    @6
    @5
    cA
    @1
    wss
    #
    wa
    #
    c0
    @2
    cun
    #
    cA
    wss
    #
    @4
    wa
    #
    wo
    @19
    cA
    c0
    @1
    cD
    ssunsn2
    @23
    @9
    @26
    @18
    @23
    @22
    @9
    @5
    @22
    @21
    biantrur
    cA
    cB
    cC
    sspr
    bitr3i
    @26
    @2
    cA
    wss
    #
    cA
    @2
    @1
    cun
    #
    wss
    #
    wa
    @10
    cA
    @2
    @7
    cun
    #
    wceq
    #
    wo
    #
    cA
    @2
    @8
    cun
    #
    wceq
    #
    cA
    @28
    wceq
    #
    wo
    #
    wo
    @18
    @25
    @27
    @4
    @29
    @24
    @2
    cA
    @24
    @2
    c0
    cun
    @2
    c0
    @2
    uncom
    @2
    un0
    eqtri
    sseq1i
    @3
    @28
    cA
    @1
    @2
    uncom
    #
    sseq2i
    anbi12i
    cA
    @2
    cB
    cC
    ssunpr
    @32
    @13
    @36
    @17
    @31
    @12
    @10
    @30
    @11
    cA
    @30
    @7
    @2
    cun
    @11
    @2
    @7
    uncom
    cB
    cD
    df-pr
    eqtr4i
    eqeq2i
    orbi2i
    @34
    @15
    @35
    @16
    @33
    @14
    cA
    @33
    @8
    @2
    cun
    @14
    @2
    @8
    uncom
    cC
    cD
    df-pr
    eqtr4i
    eqeq2i
    @28
    @0
    cA
    @0
    @3
    @28
    @20
    @37
    eqtr2i
    eqeq2i
    orbi12i
    orbi12i
    3bitri
    orbi12i
    bitri
    3bitri
end
