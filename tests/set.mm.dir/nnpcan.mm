include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "subcl.mm"
include "3adant3.mm"
include "addsub.mm"
include "eqcomd.mm"
include "syld3an1.mm"
include "npcan.mm"
include "oveq1d.mm"
include "eqtrd.mm"

theorem nnpcan
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( ( A - B ) - C ) + B ) = ( A - C ) )

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
    #
    cC
    cmin
    co
    cB
    caddc
    co
    #
    @4
    cB
    caddc
    co
    #
    cC
    cmin
    co
    #
    cA
    cC
    cmin
    co
    @4
    cc
    wcel
    #
    @1
    @0
    @2
    @5
    @7
    wceq
    @0
    @1
    @8
    @2
    cA
    cB
    subcl
    3adant3
    @8
    @1
    @2
    w3a
    @7
    @5
    @4
    cB
    cC
    addsub
    eqcomd
    syld3an1
    @3
    @6
    cA
    cC
    cmin
    @0
    @1
    @6
    cA
    wceq
    @2
    cA
    cB
    npcan
    3adant3
    oveq1d
    eqtrd
end
