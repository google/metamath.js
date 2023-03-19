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
include "divcl.mm"
include "3expb.mm"
include "mulcom.mm"
include "sylan2.mm"
include "3impb.mm"
include "div13.mm"
include "3comr.mm"
include "stoic3.mm"
include "3com23.mm"
include "3eqtrd.mm"

theorem div12
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ ( C e. CC /\ C =/= 0 ) ) -> ( A x. ( B / C ) ) = ( B x. ( A / C ) ) )

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
    cA
    cB
    cC
    cdiv
    co
    #
    cmul
    co
    #
    @5
    cA
    cmul
    co
    #
    cA
    cC
    cdiv
    co
    #
    cB
    cmul
    co
    #
    cB
    @8
    cmul
    co
    #
    @0
    @1
    @4
    @6
    @7
    wceq
    #
    @1
    @4
    wa
    @0
    @5
    cc
    wcel
    #
    @11
    @1
    @2
    @3
    @12
    cB
    cC
    divcl
    3expb
    cA
    @5
    mulcom
    sylan2
    3impb
    @1
    @4
    @0
    @7
    @9
    wceq
    cB
    cC
    cA
    div13
    3comr
    @0
    @4
    @1
    @9
    @10
    wceq
    #
    @0
    @4
    @8
    cc
    wcel
    #
    @1
    @13
    @0
    @2
    @3
    @14
    cA
    cC
    divcl
    3expb
    @8
    cB
    mulcom
    stoic3
    3com23
    3eqtrd
end
