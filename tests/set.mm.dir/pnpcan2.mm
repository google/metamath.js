include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "wceq.mm"
include "addcom.mm"
include "3adant2.mm"
include "3adant1.mm"
include "oveq12d.mm"
include "pnpcan.mm"
include "3coml.mm"
include "eqtrd.mm"

theorem pnpcan2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( A + C ) - ( B + C ) ) = ( A - B ) )

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
    cC
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
    cC
    cA
    caddc
    co
    #
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
    #
    @3
    @4
    @6
    @5
    @7
    cmin
    @0
    @2
    @4
    @6
    wceq
    @1
    cA
    cC
    addcom
    3adant2
    @1
    @2
    @5
    @7
    wceq
    @0
    cB
    cC
    addcom
    3adant1
    oveq12d
    @2
    @0
    @1
    @8
    @9
    wceq
    cC
    cA
    cB
    pnpcan
    3coml
    eqtrd
end
