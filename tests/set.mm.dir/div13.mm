include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "cdiv.mm"
include "wceq.mm"
include "mulcom.mm"
include "oveq1d.mm"
include "3adant2.mm"
include "div23.mm"
include "3com23.mm"
include "3coml.mm"
include "3eqtr3d.mm"

theorem div13
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ ( B e. CC /\ B =/= 0 ) /\ C e. CC ) -> ( ( A / B ) x. C ) = ( ( C / B ) x. A ) )

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
    w3a
    cA
    cC
    cmul
    co
    #
    cB
    cdiv
    co
    #
    cC
    cA
    cmul
    co
    #
    cB
    cdiv
    co
    #
    cA
    cB
    cdiv
    co
    cC
    cmul
    co
    #
    cC
    cB
    cdiv
    co
    cA
    cmul
    co
    #
    @0
    @2
    @4
    @6
    wceq
    @1
    @0
    @2
    wa
    @3
    @5
    cB
    cdiv
    cA
    cC
    mulcom
    oveq1d
    3adant2
    @0
    @2
    @1
    @4
    @7
    wceq
    cA
    cC
    cB
    div23
    3com23
    @2
    @0
    @1
    @6
    @8
    wceq
    cC
    cA
    cB
    div23
    3coml
    3eqtr3d
end
