include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "mulcom.mm"
include "oveq1d.mm"
include "3adant3.mm"
include "mulass.mm"
include "3com12.mm"
include "3eqtr3d.mm"

theorem mul12
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( A x. ( B x. C ) ) = ( B x. ( A x. C ) ) )

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
    cmul
    co
    #
    cC
    cmul
    co
    #
    cB
    cA
    cmul
    co
    #
    cC
    cmul
    co
    #
    cA
    cB
    cC
    cmul
    co
    cmul
    co
    cB
    cA
    cC
    cmul
    co
    cmul
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
    cmul
    cA
    cB
    mulcom
    oveq1d
    3adant3
    cA
    cB
    cC
    mulass
    @1
    @0
    @2
    @6
    @7
    wceq
    cB
    cA
    cC
    mulass
    3com12
    3eqtr3d
end
