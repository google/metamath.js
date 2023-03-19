include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "divdivdiv.mm"
include "3impdir.mm"
include "mulcom.mm"
include "adantrr.mm"
include "3adant2.mm"
include "oveq1d.mm"
include "divcan5.mm"
include "3eqtrd.mm"

theorem divcan7
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ ( B e. CC /\ B =/= 0 ) /\ ( C e. CC /\ C =/= 0 ) ) -> ( ( A / C ) / ( B / C ) ) = ( A / B ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    cB
    cc0
    wne
    wa
    #
    cC
    cc
    wcel
    #
    cC
    cc0
    wne
    #
    wa
    #
    w3a
    #
    cA
    cC
    cdiv
    co
    cB
    cC
    cdiv
    co
    cdiv
    co
    #
    cA
    cC
    cmul
    co
    #
    cC
    cB
    cmul
    co
    #
    cdiv
    co
    #
    cC
    cA
    cmul
    co
    #
    @8
    cdiv
    co
    cA
    cB
    cdiv
    co
    @0
    @4
    @1
    @6
    @9
    wceq
    cA
    cC
    cB
    cC
    divdivdiv
    3impdir
    @5
    @7
    @10
    @8
    cdiv
    @0
    @4
    @7
    @10
    wceq
    #
    @1
    @0
    @2
    @11
    @3
    cA
    cC
    mulcom
    adantrr
    3adant2
    oveq1d
    cA
    cB
    cC
    divcan5
    3eqtrd
end
