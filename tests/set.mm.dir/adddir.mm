include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "caddc.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "adddi.mm"
include "3coml.mm"
include "addcl.mm"
include "mulcom.mm"
include "stoic3.mm"
include "3adant2.mm"
include "3adant1.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"

theorem adddir
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( A + B ) x. C ) = ( ( A x. C ) + ( B x. C ) ) )

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
    #
    cC
    cA
    cB
    caddc
    co
    #
    cmul
    co
    #
    cC
    cA
    cmul
    co
    #
    cC
    cB
    cmul
    co
    #
    caddc
    co
    #
    @4
    cC
    cmul
    co
    #
    cA
    cC
    cmul
    co
    #
    cB
    cC
    cmul
    co
    #
    caddc
    co
    @2
    @0
    @1
    @5
    @8
    wceq
    cC
    cA
    cB
    adddi
    3coml
    @0
    @1
    @4
    cc
    wcel
    @2
    @9
    @5
    wceq
    cA
    cB
    addcl
    @4
    cC
    mulcom
    stoic3
    @3
    @10
    @6
    @11
    @7
    caddc
    @0
    @2
    @10
    @6
    wceq
    @1
    cA
    cC
    mulcom
    3adant2
    @1
    @2
    @11
    @7
    wceq
    @0
    cB
    cC
    mulcom
    3adant1
    oveq12d
    3eqtr4d
end
