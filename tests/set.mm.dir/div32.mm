include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "w3a.mm"
include "div23.mm"
include "divass.mm"
include "eqtr3d.mm"
include "3com23.mm"

theorem div32
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ ( B e. CC /\ B =/= 0 ) /\ C e. CC ) -> ( ( A / B ) x. C ) = ( A x. ( C / B ) ) )

  proof
    cA
    cc
    wcel
    #
    cC
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
    cA
    cB
    cdiv
    co
    cC
    cmul
    co
    #
    cA
    cC
    cB
    cdiv
    co
    cmul
    co
    #
    wceq
    @0
    @1
    @2
    w3a
    cA
    cC
    cmul
    co
    cB
    cdiv
    co
    @3
    @4
    cA
    cC
    cB
    div23
    cA
    cC
    cB
    divass
    eqtr3d
    3com23
end
