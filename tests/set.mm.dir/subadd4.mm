include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "subcl.mm"
include "subsub2.mm"
include "3expb.mm"
include "sylan.mm"
include "addsub4.mm"
include "an42s.mm"
include "eqtr4d.mm"

theorem subadd4
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. CC /\ B e. CC ) /\ ( C e. CC /\ D e. CC ) ) -> ( ( A - B ) - ( C - D ) ) = ( ( A + D ) - ( B + C ) ) )

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
    cmin
    co
    #
    cC
    cD
    cmin
    co
    cmin
    co
    #
    @6
    cD
    cC
    cmin
    co
    caddc
    co
    #
    cA
    cD
    caddc
    co
    cB
    cC
    caddc
    co
    cmin
    co
    #
    @2
    @6
    cc
    wcel
    #
    @5
    @7
    @8
    wceq
    #
    cA
    cB
    subcl
    @10
    @3
    @4
    @11
    @6
    cC
    cD
    subsub2
    3expb
    sylan
    @0
    @4
    @1
    @3
    @9
    @8
    wceq
    cA
    cD
    cB
    cC
    addsub4
    an42s
    eqtr4d
end
