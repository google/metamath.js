include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "wceq.mm"
include "simp1.mm"
include "simp2.mm"
include "addcld.mm"
include "simp3.mm"
include "subsub.mm"
include "syl3anc.mm"
include "pncan2.mm"
include "3adant3.mm"
include "oveq1d.mm"
include "eqtrd.mm"

theorem pnncan
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( A + B ) - ( A - C ) ) = ( B + C ) )

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
    cA
    cC
    cmin
    co
    cmin
    co
    #
    @4
    cA
    cmin
    co
    #
    cC
    caddc
    co
    #
    cB
    cC
    caddc
    co
    @3
    @4
    cc
    wcel
    @0
    @2
    @5
    @7
    wceq
    @3
    cA
    cB
    @0
    @1
    @2
    simp1
    #
    @0
    @1
    @2
    simp2
    addcld
    @8
    @0
    @1
    @2
    simp3
    @4
    cA
    cC
    subsub
    syl3anc
    @3
    @6
    cB
    cC
    caddc
    @0
    @1
    @6
    cB
    wceq
    @2
    cA
    cB
    pncan2
    3adant3
    oveq1d
    eqtrd
end
