include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "wceq.mm"
include "addcl.mm"
include "3adant1.mm"
include "subsub.mm"
include "syld3an2.mm"
include "pncan.mm"
include "oveq2d.mm"
include "eqtr3d.mm"

theorem nppcan2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( A - ( B + C ) ) + C ) = ( A - B ) )

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
    cC
    cmin
    co
    #
    cmin
    co
    #
    cA
    @4
    cmin
    co
    cC
    caddc
    co
    #
    cA
    cB
    cmin
    co
    @0
    @4
    cc
    wcel
    #
    @1
    @2
    @6
    @7
    wceq
    @1
    @2
    @8
    @0
    cB
    cC
    addcl
    3adant1
    cA
    @4
    cC
    subsub
    syld3an2
    @3
    @5
    cB
    cA
    cmin
    @1
    @2
    @5
    cB
    wceq
    @0
    cB
    cC
    pncan
    3adant1
    oveq2d
    eqtr3d
end
