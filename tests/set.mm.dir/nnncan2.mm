include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "wceq.mm"
include "subcl.mm"
include "3adant1.mm"
include "sub32.mm"
include "syld3an2.mm"
include "nnncan.mm"
include "eqtr3d.mm"

theorem nnncan2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( A - C ) - ( B - C ) ) = ( A - B ) )

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
    cC
    cmin
    co
    #
    cmin
    co
    cC
    cmin
    co
    #
    cA
    cC
    cmin
    co
    @3
    cmin
    co
    #
    cA
    cB
    cmin
    co
    @0
    @3
    cc
    wcel
    #
    @1
    @2
    @4
    @5
    wceq
    @1
    @2
    @6
    @0
    cB
    cC
    subcl
    3adant1
    cA
    @3
    cC
    sub32
    syld3an2
    cA
    cB
    cC
    nnncan
    eqtr3d
end
