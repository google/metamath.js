include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cdiv.mm"
include "wceq.mm"
include "simp3l.mm"
include "simp1.mm"
include "mulcld.mm"
include "divdir.mm"
include "syld3an1.mm"
include "3anass.mm"
include "biimpri.mm"
include "3adant2.mm"
include "divcan3.mm"
include "syl.mm"
include "oveq1d.mm"
include "eqtrd.mm"

theorem muldivdir
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ ( C e. CC /\ C =/= 0 ) ) -> ( ( ( C x. A ) + B ) / C ) = ( A + ( B / C ) ) )

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
    cC
    cc0
    wne
    #
    wa
    #
    w3a
    #
    cC
    cA
    cmul
    co
    #
    cB
    caddc
    co
    cC
    cdiv
    co
    #
    @6
    cC
    cdiv
    co
    #
    cB
    cC
    cdiv
    co
    #
    caddc
    co
    #
    cA
    @9
    caddc
    co
    @6
    cc
    wcel
    @1
    @0
    @4
    @7
    @10
    wceq
    @5
    cC
    cA
    @0
    @1
    @2
    @3
    simp3l
    @0
    @1
    @4
    simp1
    mulcld
    @6
    cB
    cC
    divdir
    syld3an1
    @5
    @8
    cA
    @9
    caddc
    @5
    @0
    @2
    @3
    w3a
    #
    @8
    cA
    wceq
    @0
    @4
    @11
    @1
    @11
    @0
    @4
    wa
    @0
    @2
    @3
    3anass
    biimpri
    3adant2
    cA
    cC
    divcan3
    syl
    oveq1d
    eqtrd
end
