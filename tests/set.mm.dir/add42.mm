include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "add4.mm"
include "wceq.mm"
include "addcom.mm"
include "ad2ant2l.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem add42
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. CC /\ B e. CC ) /\ ( C e. CC /\ D e. CC ) ) -> ( ( A + B ) + ( C + D ) ) = ( ( A + C ) + ( D + B ) ) )

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
    cB
    caddc
    co
    cC
    cD
    caddc
    co
    caddc
    co
    cA
    cC
    caddc
    co
    #
    cB
    cD
    caddc
    co
    #
    caddc
    co
    @5
    cD
    cB
    caddc
    co
    #
    caddc
    co
    cA
    cB
    cC
    cD
    add4
    @4
    @6
    @7
    @5
    caddc
    @1
    @3
    @6
    @7
    wceq
    @0
    @2
    cB
    cD
    addcom
    ad2ant2l
    oveq2d
    eqtrd
end
