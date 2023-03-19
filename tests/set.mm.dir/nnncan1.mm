include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "wceq.mm"
include "subcl.mm"
include "3adant2.mm"
include "sub32.mm"
include "syld3an3.mm"
include "nncan.mm"
include "oveq1d.mm"
include "eqtrd.mm"

theorem nnncan1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( A - B ) - ( A - C ) ) = ( C - B ) )

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
    cmin
    co
    cA
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
    #
    cB
    cmin
    co
    #
    cC
    cB
    cmin
    co
    @0
    @1
    @2
    @4
    cc
    wcel
    #
    @5
    @7
    wceq
    @0
    @2
    @8
    @1
    cA
    cC
    subcl
    3adant2
    cA
    cB
    @4
    sub32
    syld3an3
    @3
    @6
    cC
    cB
    cmin
    @0
    @2
    @6
    cC
    wceq
    @1
    cA
    cC
    nncan
    3adant2
    oveq1d
    eqtrd
end
