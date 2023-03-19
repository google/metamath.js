include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "ccxp.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wne.mm"
include "cxpne0.mm"
include "3com23.mm"
include "3expia.mm"
include "necon4d.mm"
include "c1.mm"
include "ax-1ne0.mm"
include "cxp0.mm"
include "neeq1d.mm"
include "mpbiri.mm"
include "adantr.mm"
include "oveq2.mm"
include "syl5ibrcom.mm"
include "necon2d.mm"
include "jcad.mm"
include "wi.mm"
include "0cxp.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "expimpd.mm"
include "ancomsd.mm"
include "adantl.mm"
include "impbid.mm"

theorem cxpeq0
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( ( A ^c B ) = 0 <-> ( A = 0 /\ B =/= 0 ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    cA
    cB
    ccxp
    co
    #
    cc0
    wceq
    #
    cA
    cc0
    wceq
    #
    cB
    cc0
    wne
    #
    wa
    #
    @2
    @4
    @5
    @6
    @2
    cA
    cc0
    @3
    cc0
    @0
    @1
    cA
    cc0
    wne
    #
    @3
    cc0
    wne
    #
    @0
    @8
    @1
    @9
    cA
    cB
    cxpne0
    3com23
    3expia
    necon4d
    @2
    cB
    cc0
    @3
    cc0
    @2
    @9
    cB
    cc0
    wceq
    #
    cA
    cc0
    ccxp
    co
    #
    cc0
    wne
    #
    @0
    @12
    @1
    @0
    @12
    c1
    cc0
    wne
    ax-1ne0
    @0
    @11
    c1
    cc0
    cA
    cxp0
    neeq1d
    mpbiri
    adantr
    @10
    @3
    @11
    cc0
    cB
    cc0
    cA
    ccxp
    oveq2
    neeq1d
    syl5ibrcom
    necon2d
    jcad
    @1
    @7
    @4
    wi
    @0
    @1
    @6
    @5
    @4
    @1
    @6
    @5
    @4
    @1
    @6
    wa
    @4
    @5
    cc0
    cB
    ccxp
    co
    #
    cc0
    wceq
    cB
    0cxp
    @5
    @3
    @13
    cc0
    cA
    cc0
    cB
    ccxp
    oveq1
    eqeq1d
    syl5ibrcom
    expimpd
    ancomsd
    adantl
    impbid
end
