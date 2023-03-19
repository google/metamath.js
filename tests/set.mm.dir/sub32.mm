include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "wceq.mm"
include "addcom.mm"
include "3adant1.mm"
include "oveq2d.mm"
include "subsub4.mm"
include "3com23.mm"
include "3eqtr4d.mm"

theorem sub32
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( A - B ) - C ) = ( ( A - C ) - B ) )

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
    cA
    cB
    cC
    caddc
    co
    #
    cmin
    co
    cA
    cC
    cB
    caddc
    co
    #
    cmin
    co
    #
    cA
    cB
    cmin
    co
    cC
    cmin
    co
    cA
    cC
    cmin
    co
    cB
    cmin
    co
    #
    @3
    @4
    @5
    cA
    cmin
    @1
    @2
    @4
    @5
    wceq
    @0
    cB
    cC
    addcom
    3adant1
    oveq2d
    cA
    cB
    cC
    subsub4
    @0
    @2
    @1
    @7
    @6
    wceq
    cA
    cC
    cB
    subsub4
    3com23
    3eqtr4d
end
