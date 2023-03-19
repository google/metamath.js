include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "wne.mm"
include "simpr.mm"
include "adantr.mm"
include "mul02d.mm"
include "eqeq2d.mm"
include "simpl.mm"
include "0cnd.mm"
include "mulcan2d.mm"
include "bitr3d.mm"
include "biimpd.mm"
include "impancom.mm"
include "necon1bd.mm"
include "orrd.mm"
include "ex.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "mul01d.mm"
include "oveq2.mm"
include "jaod.mm"
include "impbid.mm"

theorem mul0or
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( ( A x. B ) = 0 <-> ( A = 0 \/ B = 0 ) ) )

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
    cmul
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
    wceq
    #
    wo
    #
    @2
    @4
    @7
    @2
    @4
    wa
    #
    @5
    @6
    @8
    @5
    cB
    cc0
    @2
    cB
    cc0
    wne
    #
    @4
    @5
    @2
    @9
    wa
    #
    @4
    @5
    @10
    @3
    cc0
    cB
    cmul
    co
    #
    wceq
    @4
    @5
    @10
    @11
    cc0
    @3
    @10
    cB
    @2
    @1
    @9
    @0
    @1
    simpr
    #
    adantr
    #
    mul02d
    eqeq2d
    @10
    cA
    cc0
    cB
    @2
    @0
    @9
    @0
    @1
    simpl
    #
    adantr
    @10
    0cnd
    @13
    @2
    @9
    simpr
    mulcan2d
    bitr3d
    biimpd
    impancom
    necon1bd
    orrd
    ex
    @2
    @5
    @4
    @6
    @2
    @4
    @5
    @11
    cc0
    wceq
    @2
    cB
    @12
    mul02d
    @5
    @3
    @11
    cc0
    cA
    cc0
    cB
    cmul
    oveq1
    eqeq1d
    syl5ibrcom
    @2
    @4
    @6
    cA
    cc0
    cmul
    co
    #
    cc0
    wceq
    @2
    cA
    @14
    mul01d
    @6
    @3
    @15
    cc0
    cB
    cc0
    cA
    cmul
    oveq2
    eqeq1d
    syl5ibrcom
    jaod
    impbid
end
