include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "add12.mm"
include "3expb.mm"
include "oveq2d.mm"
include "adantll.mm"
include "addcl.mm"
include "addass.mm"
include "3expa.mm"
include "sylan2.mm"
include "an4s.mm"
include "3eqtr4d.mm"

theorem add4
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. CC /\ B e. CC ) /\ ( C e. CC /\ D e. CC ) ) -> ( ( A + B ) + ( C + D ) ) = ( ( A + C ) + ( B + D ) ) )

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
    #
    cC
    cc
    wcel
    #
    cD
    cc
    wcel
    #
    wa
    #
    wa
    cA
    cB
    cC
    cD
    caddc
    co
    #
    caddc
    co
    #
    caddc
    co
    #
    cA
    cC
    cB
    cD
    caddc
    co
    #
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
    @6
    caddc
    co
    #
    cA
    cC
    caddc
    co
    @9
    caddc
    co
    #
    @1
    @5
    @8
    @11
    wceq
    @0
    @1
    @5
    wa
    @7
    @10
    cA
    caddc
    @1
    @3
    @4
    @7
    @10
    wceq
    cB
    cC
    cD
    add12
    3expb
    oveq2d
    adantll
    @5
    @2
    @6
    cc
    wcel
    #
    @12
    @8
    wceq
    #
    cC
    cD
    addcl
    @0
    @1
    @14
    @15
    cA
    cB
    @6
    addass
    3expa
    sylan2
    @0
    @3
    @1
    @4
    @13
    @11
    wceq
    #
    @1
    @4
    wa
    @0
    @3
    wa
    @9
    cc
    wcel
    #
    @16
    cB
    cD
    addcl
    @0
    @3
    @17
    @16
    cA
    cC
    @9
    addass
    3expa
    sylan2
    an4s
    3eqtr4d
end
