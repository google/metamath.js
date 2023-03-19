include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "wne.mm"
include "cmul.mm"
include "co.mm"
include "cdiv.mm"
include "wceq.mm"
include "mulcom.mm"
include "adantr.mm"
include "oveq1d.mm"
include "divmuldiv.mm"
include "ancom1s.mm"
include "3eqtr4d.mm"

theorem divmul13
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. CC /\ B e. CC ) /\ ( ( C e. CC /\ C =/= 0 ) /\ ( D e. CC /\ D =/= 0 ) ) ) -> ( ( A / C ) x. ( B / D ) ) = ( ( B / C ) x. ( A / D ) ) )

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
    cC
    cc
    wcel
    cC
    cc0
    wne
    wa
    cD
    cc
    wcel
    cD
    cc0
    wne
    wa
    wa
    #
    wa
    #
    cA
    cB
    cmul
    co
    #
    cC
    cD
    cmul
    co
    #
    cdiv
    co
    cB
    cA
    cmul
    co
    #
    @6
    cdiv
    co
    #
    cA
    cC
    cdiv
    co
    cB
    cD
    cdiv
    co
    cmul
    co
    cB
    cC
    cdiv
    co
    cA
    cD
    cdiv
    co
    cmul
    co
    #
    @4
    @5
    @7
    @6
    cdiv
    @2
    @5
    @7
    wceq
    @3
    cA
    cB
    mulcom
    adantr
    oveq1d
    cA
    cB
    cC
    cD
    divmuldiv
    @1
    @0
    @3
    @9
    @8
    wceq
    cB
    cA
    cC
    cD
    divmuldiv
    ancom1s
    3eqtr4d
end
