include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpr.mm"
include "divass.mm"
include "syl3anc.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "mulcl.mm"
include "3adant3.mm"
include "adantr.mm"
include "simpl3.mm"
include "div32.mm"
include "eqtrd.mm"

theorem divmulass
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. CC /\ B e. CC /\ C e. CC ) /\ ( D e. CC /\ D =/= 0 ) ) -> ( ( A x. ( B / D ) ) x. C ) = ( ( A x. B ) x. ( C / D ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cC
    cc
    wcel
    #
    w3a
    #
    cD
    cc
    wcel
    cD
    cc0
    wne
    wa
    #
    wa
    #
    cA
    cB
    cD
    cdiv
    co
    cmul
    co
    #
    cC
    cmul
    co
    cA
    cB
    cmul
    co
    #
    cD
    cdiv
    co
    #
    cC
    cmul
    co
    #
    @7
    cC
    cD
    cdiv
    co
    cmul
    co
    #
    @5
    @6
    @8
    cC
    cmul
    @5
    @8
    @6
    @5
    @0
    @1
    @4
    @8
    @6
    wceq
    @0
    @1
    @2
    @4
    simpl1
    @0
    @1
    @2
    @4
    simpl2
    @3
    @4
    simpr
    #
    cA
    cB
    cD
    divass
    syl3anc
    eqcomd
    oveq1d
    @5
    @7
    cc
    wcel
    #
    @4
    @2
    @9
    @10
    wceq
    @3
    @12
    @4
    @0
    @1
    @12
    @2
    cA
    cB
    mulcl
    3adant3
    adantr
    @11
    @0
    @1
    @2
    @4
    simpl3
    @7
    cD
    cC
    div32
    syl3anc
    eqtrd
end
