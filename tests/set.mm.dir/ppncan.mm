include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "wceq.mm"
include "addcom.mm"
include "3adant3.mm"
include "oveq1d.mm"
include "addcl.mm"
include "subsub2.mm"
include "syld3an1.mm"
include "pnncan.mm"
include "3com12.mm"
include "3eqtr3d.mm"

theorem ppncan
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( A + B ) + ( C - B ) ) = ( A + C ) )

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
    caddc
    co
    #
    cB
    cC
    cmin
    co
    #
    cmin
    co
    #
    cB
    cA
    caddc
    co
    #
    @5
    cmin
    co
    #
    @4
    cC
    cB
    cmin
    co
    caddc
    co
    #
    cA
    cC
    caddc
    co
    #
    @3
    @4
    @7
    @5
    cmin
    @0
    @1
    @4
    @7
    wceq
    @2
    cA
    cB
    addcom
    3adant3
    oveq1d
    @4
    cc
    wcel
    #
    @1
    @0
    @2
    @6
    @9
    wceq
    @0
    @1
    @11
    @2
    cA
    cB
    addcl
    3adant3
    @4
    cB
    cC
    subsub2
    syld3an1
    @1
    @0
    @2
    @8
    @10
    wceq
    cB
    cA
    cC
    pnncan
    3com12
    3eqtr3d
end
