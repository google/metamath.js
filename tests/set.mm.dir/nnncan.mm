include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "subcl.mm"
include "3adant1.mm"
include "subsub4.mm"
include "syld3an2.mm"
include "wa.mm"
include "npcan.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem nnncan
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( A - ( B - C ) ) - C ) = ( A - B ) )

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
    @3
    cC
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
    @0
    @3
    cc
    wcel
    #
    @1
    @2
    @4
    @6
    wceq
    @1
    @2
    @8
    @0
    cB
    cC
    subcl
    3adant1
    cA
    @3
    cC
    subsub4
    syld3an2
    @1
    @2
    @6
    @7
    wceq
    @0
    @1
    @2
    wa
    @5
    cB
    cA
    cmin
    cB
    cC
    npcan
    oveq2d
    3adant1
    eqtrd
end
