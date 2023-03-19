include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "addcom.mm"
include "oveq2d.mm"
include "3adant1.mm"
include "addass.mm"
include "3com23.mm"
include "3eqtr4d.mm"

theorem add32
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( A + B ) + C ) = ( ( A + C ) + B ) )

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
    cA
    cB
    cC
    caddc
    co
    #
    caddc
    co
    #
    cA
    cC
    cB
    caddc
    co
    #
    caddc
    co
    #
    cA
    cB
    caddc
    co
    cC
    caddc
    co
    cA
    cC
    caddc
    co
    cB
    caddc
    co
    #
    @1
    @2
    @4
    @6
    wceq
    @0
    @1
    @2
    wa
    @3
    @5
    cA
    caddc
    cB
    cC
    addcom
    oveq2d
    3adant1
    cA
    cB
    cC
    addass
    @0
    @2
    @1
    @7
    @6
    wceq
    cA
    cC
    cB
    addass
    3com23
    3eqtr4d
end
