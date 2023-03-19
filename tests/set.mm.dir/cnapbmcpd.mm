include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "addcl.mm"
include "adantr.mm"
include "simpr.mm"
include "adantl.mm"
include "simpl.mm"
include "addsubd.mm"
include "add32d.mm"
include "oveq1d.mm"
include "eqtr3d.mm"

theorem cnapbmcpd
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( ( A e. CC /\ B e. CC ) /\ ( C e. CC /\ D e. CC ) ) -> ( ( ( A + B ) - C ) + D ) = ( ( ( A + D ) + B ) - C ) )

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
    #
    cA
    cB
    caddc
    co
    #
    cD
    caddc
    co
    #
    cC
    cmin
    co
    @7
    cC
    cmin
    co
    cD
    caddc
    co
    cA
    cD
    caddc
    co
    cB
    caddc
    co
    #
    cC
    cmin
    co
    @6
    @7
    cD
    cC
    @2
    @7
    cc
    wcel
    @5
    cA
    cB
    addcl
    adantr
    @5
    @4
    @2
    @3
    @4
    simpr
    adantl
    #
    @5
    @3
    @2
    @3
    @4
    simpl
    adantl
    addsubd
    @6
    @8
    @9
    cC
    cmin
    @6
    cA
    cB
    cD
    @2
    @0
    @5
    @0
    @1
    simpl
    adantr
    @2
    @1
    @5
    @0
    @1
    simpr
    adantr
    @10
    add32d
    oveq1d
    eqtr3d
end
