include "cc.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "w3a.mm"
include "subadd23.mm"
include "subcl.mm"
include "addcom.mm"
include "stoic3.mm"
include "eqtr3d.mm"
include "3com23.mm"

theorem addsub12
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( A + ( B - C ) ) = ( B + ( A - C ) ) )

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
    #
    cA
    cB
    cC
    cmin
    co
    caddc
    co
    #
    cB
    cA
    cC
    cmin
    co
    #
    caddc
    co
    #
    wceq
    @0
    @1
    @2
    w3a
    @4
    cB
    caddc
    co
    #
    @3
    @5
    cA
    cC
    cB
    subadd23
    @0
    @1
    @4
    cc
    wcel
    @2
    @6
    @5
    wceq
    cA
    cC
    subcl
    @4
    cB
    addcom
    stoic3
    eqtr3d
    3com23
end
