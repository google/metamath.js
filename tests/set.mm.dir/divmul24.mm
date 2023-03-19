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
include "ad2ant2r.mm"
include "adantl.mm"
include "oveq2d.mm"
include "divmuldiv.mm"
include "ancom2s.mm"
include "3eqtr4d.mm"

theorem divmul24
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. CC /\ B e. CC ) /\ ( ( C e. CC /\ C =/= 0 ) /\ ( D e. CC /\ D =/= 0 ) ) ) -> ( ( A / C ) x. ( B / D ) ) = ( ( A / D ) x. ( B / C ) ) )

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
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
    cD
    cc
    wcel
    #
    cD
    cc0
    wne
    #
    wa
    #
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
    @9
    cD
    cC
    cmul
    co
    #
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
    cA
    cD
    cdiv
    co
    cB
    cC
    cdiv
    co
    cmul
    co
    #
    @8
    @10
    @11
    @9
    cdiv
    @7
    @10
    @11
    wceq
    #
    @0
    @1
    @4
    @14
    @2
    @5
    cC
    cD
    mulcom
    ad2ant2r
    adantl
    oveq2d
    cA
    cB
    cC
    cD
    divmuldiv
    @0
    @6
    @3
    @13
    @12
    wceq
    cA
    cB
    cD
    cC
    divmuldiv
    ancom2s
    3eqtr4d
end
