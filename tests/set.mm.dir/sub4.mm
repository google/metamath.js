include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "wceq.mm"
include "addcom.mm"
include "ad2ant2lr.mm"
include "oveq2d.mm"
include "subadd4.mm"
include "an4s.mm"
include "3eqtr4d.mm"

theorem sub4
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. CC /\ B e. CC ) /\ ( C e. CC /\ D e. CC ) ) -> ( ( A - B ) - ( C - D ) ) = ( ( A - C ) - ( B - D ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    cC
    cc
    wcel
    #
    cD
    cc
    wcel
    #
    wa
    wa
    #
    cA
    cD
    caddc
    co
    #
    cB
    cC
    caddc
    co
    #
    cmin
    co
    @5
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
    cD
    cmin
    co
    cmin
    co
    cA
    cC
    cmin
    co
    cB
    cD
    cmin
    co
    cmin
    co
    #
    @4
    @6
    @7
    @5
    cmin
    @1
    @2
    @6
    @7
    wceq
    @0
    @3
    cB
    cC
    addcom
    ad2ant2lr
    oveq2d
    cA
    cB
    cC
    cD
    subadd4
    @0
    @2
    @1
    @3
    @9
    @8
    wceq
    cA
    cC
    cB
    cD
    subadd4
    an4s
    3eqtr4d
end
