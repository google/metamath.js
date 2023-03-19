include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "wceq.mm"
include "add32.mm"
include "3expa.mm"
include "adantrr.mm"
include "oveq1d.mm"
include "addcl.mm"
include "addsub.mm"
include "3expb.mm"
include "sylan.mm"
include "an4s.mm"
include "eqtrd.mm"

theorem 2addsub
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. CC /\ B e. CC ) /\ ( C e. CC /\ D e. CC ) ) -> ( ( ( A + B ) + C ) - D ) = ( ( ( A + C ) - D ) + B ) )

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
    wa
    #
    cA
    cB
    caddc
    co
    cC
    caddc
    co
    #
    cD
    cmin
    co
    cA
    cC
    caddc
    co
    #
    cB
    caddc
    co
    #
    cD
    cmin
    co
    #
    @7
    cD
    cmin
    co
    cB
    caddc
    co
    #
    @5
    @6
    @8
    cD
    cmin
    @2
    @3
    @6
    @8
    wceq
    #
    @4
    @0
    @1
    @3
    @11
    cA
    cB
    cC
    add32
    3expa
    adantrr
    oveq1d
    @0
    @3
    @1
    @4
    @9
    @10
    wceq
    #
    @0
    @3
    wa
    @7
    cc
    wcel
    #
    @1
    @4
    wa
    @12
    cA
    cC
    addcl
    @13
    @1
    @4
    @12
    @7
    cB
    cD
    addsub
    3expb
    sylan
    an4s
    eqtrd
end
