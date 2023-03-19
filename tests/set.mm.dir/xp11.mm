include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cxp.mm"
include "wceq.mm"
include "wi.mm"
include "xpnz.mm"
include "anidm.mm"
include "neeq1.mm"
include "anbi2d.mm"
include "syl5bbr.mm"
include "wss.mm"
include "eqimss.mm"
include "ssxpb.mm"
include "syl5ibcom.mm"
include "eqimss2.mm"
include "anim12d.mm"
include "an4.mm"
include "eqss.mm"
include "anbi12i.mm"
include "bitr4i.mm"
include "syl6ib.mm"
include "sylbid.mm"
include "com12.mm"
include "sylbi.mm"
include "xpeq12.mm"
include "impbid1.mm"

theorem xp11
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( A =/= (/) /\ B =/= (/) ) -> ( ( A X. B ) = ( C X. D ) <-> ( A = C /\ B = D ) ) )

  proof
    cA
    c0
    wne
    cB
    c0
    wne
    wa
    #
    cA
    cB
    cxp
    #
    cC
    cD
    cxp
    #
    wceq
    #
    cA
    cC
    wceq
    #
    cB
    cD
    wceq
    #
    wa
    #
    @0
    @1
    c0
    wne
    #
    @3
    @6
    wi
    cA
    cB
    xpnz
    @3
    @7
    @6
    @3
    @7
    @7
    @2
    c0
    wne
    #
    wa
    #
    @6
    @7
    @7
    @7
    wa
    @3
    @9
    @7
    anidm
    @3
    @7
    @8
    @7
    @1
    @2
    c0
    neeq1
    anbi2d
    syl5bbr
    @3
    @9
    cA
    cC
    wss
    #
    cB
    cD
    wss
    #
    wa
    #
    cC
    cA
    wss
    #
    cD
    cB
    wss
    #
    wa
    #
    wa
    #
    @6
    @3
    @7
    @12
    @8
    @15
    @3
    @1
    @2
    wss
    @7
    @12
    @1
    @2
    eqimss
    cA
    cB
    cC
    cD
    ssxpb
    syl5ibcom
    @3
    @2
    @1
    wss
    @8
    @15
    @2
    @1
    eqimss2
    cC
    cD
    cA
    cB
    ssxpb
    syl5ibcom
    anim12d
    @16
    @10
    @13
    wa
    #
    @11
    @14
    wa
    #
    wa
    @6
    @10
    @11
    @13
    @14
    an4
    @4
    @17
    @5
    @18
    cA
    cC
    eqss
    cB
    cD
    eqss
    anbi12i
    bitr4i
    syl6ib
    sylbid
    com12
    sylbi
    cA
    cC
    cB
    cD
    xpeq12
    impbid1
end
