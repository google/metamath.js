include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "mulcom.mm"
include "oveq2d.mm"
include "3adant1.mm"
include "mulass.mm"
include "3com23.mm"
include "3eqtr4d.mm"

theorem mul32
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( A x. B ) x. C ) = ( ( A x. C ) x. B ) )

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
    cmul
    co
    #
    cmul
    co
    #
    cA
    cC
    cB
    cmul
    co
    #
    cmul
    co
    #
    cA
    cB
    cmul
    co
    cC
    cmul
    co
    cA
    cC
    cmul
    co
    cB
    cmul
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
    cmul
    cB
    cC
    mulcom
    oveq2d
    3adant1
    cA
    cB
    cC
    mulass
    @0
    @2
    @1
    @7
    @6
    wceq
    cA
    cC
    cB
    mulass
    3com23
    3eqtr4d
end
