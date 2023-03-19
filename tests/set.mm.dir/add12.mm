include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "addcom.mm"
include "oveq1d.mm"
include "3adant3.mm"
include "addass.mm"
include "3com12.mm"
include "3eqtr3d.mm"

theorem add12
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( A + ( B + C ) ) = ( B + ( A + C ) ) )

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
    caddc
    co
    #
    cC
    caddc
    co
    #
    cB
    cA
    caddc
    co
    #
    cC
    caddc
    co
    #
    cA
    cB
    cC
    caddc
    co
    caddc
    co
    cB
    cA
    cC
    caddc
    co
    caddc
    co
    #
    @0
    @1
    @4
    @6
    wceq
    @2
    @0
    @1
    wa
    @3
    @5
    cC
    caddc
    cA
    cB
    addcom
    oveq1d
    3adant3
    cA
    cB
    cC
    addass
    @1
    @0
    @2
    @6
    @7
    wceq
    cB
    cA
    cC
    addass
    3com12
    3eqtr3d
end
