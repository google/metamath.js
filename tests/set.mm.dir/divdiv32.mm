include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "reccl.mm"
include "div23.mm"
include "syl3an2.mm"
include "divrec.mm"
include "3expb.mm"
include "3adant3.mm"
include "oveq1d.mm"
include "divcl.mm"
include "syl3an1.mm"
include "3impa.mm"
include "3com23.mm"
include "3eqtr4d.mm"

theorem divdiv32
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ ( B e. CC /\ B =/= 0 ) /\ ( C e. CC /\ C =/= 0 ) ) -> ( ( A / B ) / C ) = ( ( A / C ) / B ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
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
    c1
    cB
    cdiv
    co
    #
    cmul
    co
    #
    cC
    cdiv
    co
    #
    cA
    cC
    cdiv
    co
    #
    @8
    cmul
    co
    #
    cA
    cB
    cdiv
    co
    #
    cC
    cdiv
    co
    @11
    cB
    cdiv
    co
    #
    @3
    @0
    @8
    cc
    wcel
    @6
    @10
    @12
    wceq
    cB
    reccl
    cA
    @8
    cC
    div23
    syl3an2
    @7
    @13
    @9
    cC
    cdiv
    @0
    @3
    @13
    @9
    wceq
    #
    @6
    @0
    @1
    @2
    @15
    cA
    cB
    divrec
    3expb
    3adant3
    oveq1d
    @0
    @6
    @3
    @14
    @12
    wceq
    #
    @0
    @6
    @3
    @16
    @0
    @6
    wa
    #
    @1
    @2
    @16
    @17
    @11
    cc
    wcel
    #
    @1
    @2
    @16
    @0
    @4
    @5
    @18
    cA
    cC
    divcl
    3expb
    @11
    cB
    divrec
    syl3an1
    3expb
    3impa
    3com23
    3eqtr4d
end
