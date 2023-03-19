include "wne.mm"
include "cin.mm"
include "wss.mm"
include "wa.mm"
include "wo.mm"
include "wpss.mm"
include "wn.mm"
include "wceq.mm"
include "nne.mm"
include "neeq1.mm"
include "biimprcd.mm"
include "syl5bi.mm"
include "orrd.mm"
include "inss1.mm"
include "jctl.mm"
include "inss2.mm"
include "orim12i.mm"
include "syl.mm"
include "inidm.mm"
include "ineq2.mm"
include "syl5reqr.mm"
include "necon3i.mm"
include "adantl.mm"
include "ineq1.mm"
include "syl6eq.mm"
include "jaoi.mm"
include "impbii.mm"
include "df-pss.mm"
include "orbi12i.mm"
include "bitr4i.mm"

theorem nepss
  let cA: class A
  let cB: class B


  assert |- ( A =/= B <-> ( ( A i^i B ) C. A \/ ( A i^i B ) C. B ) )

  proof
    cA
    cB
    wne
    #
    cA
    cB
    cin
    #
    cA
    wss
    #
    @1
    cA
    wne
    #
    wa
    #
    @1
    cB
    wss
    #
    @1
    cB
    wne
    #
    wa
    #
    wo
    #
    @1
    cA
    wpss
    #
    @1
    cB
    wpss
    #
    wo
    @0
    @8
    @0
    @3
    @6
    wo
    @8
    @0
    @3
    @6
    @3
    wn
    @1
    cA
    wceq
    #
    @0
    @6
    @1
    cA
    nne
    @11
    @6
    @0
    @1
    cA
    cB
    neeq1
    biimprcd
    syl5bi
    orrd
    @3
    @4
    @6
    @7
    @3
    @2
    cA
    cB
    inss1
    jctl
    @6
    @5
    cA
    cB
    inss2
    jctl
    orim12i
    syl
    @4
    @0
    @7
    @3
    @0
    @2
    cA
    cB
    @1
    cA
    cA
    cB
    wceq
    #
    cA
    cA
    cA
    cin
    @1
    cA
    inidm
    cA
    cB
    cA
    ineq2
    syl5reqr
    necon3i
    adantl
    @6
    @0
    @5
    cA
    cB
    @1
    cB
    @12
    @1
    cB
    cB
    cin
    cB
    cA
    cB
    cB
    ineq1
    cB
    inidm
    syl6eq
    necon3i
    adantl
    jaoi
    impbii
    @9
    @4
    @10
    @7
    @1
    cA
    df-pss
    @1
    cB
    df-pss
    orbi12i
    bitr4i
end
