include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "wceq.mm"
include "wa.mm"
include "addcom.mm"
include "oveq1d.mm"
include "3adant3.mm"
include "addsubass.mm"
include "3com12.mm"
include "subcl.mm"
include "sylan2.mm"
include "3impb.mm"
include "3eqtrd.mm"

theorem addsub
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( A + B ) - C ) = ( ( A - C ) + B ) )

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
    caddc
    co
    #
    cC
    cmin
    co
    #
    cB
    cA
    caddc
    co
    #
    cC
    cmin
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
    @7
    cB
    caddc
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
    cmin
    cA
    cB
    addcom
    oveq1d
    3adant3
    @1
    @0
    @2
    @6
    @8
    wceq
    cB
    cA
    cC
    addsubass
    3com12
    @1
    @0
    @2
    @8
    @9
    wceq
    #
    @1
    @0
    @2
    @10
    @0
    @2
    wa
    @1
    @7
    cc
    wcel
    @10
    cA
    cC
    subcl
    cB
    @7
    addcom
    sylan2
    3impb
    3com12
    3eqtrd
end
