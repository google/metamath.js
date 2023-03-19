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
include "subsub4.mm"
include "syl3anc.mm"
include "pncan2.mm"
include "3adant3.mm"
include "oveq1d.mm"
include "eqtr3d.mm"

theorem pnpcan
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( A + B ) - ( A + C ) ) = ( B - C ) )

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
    cmin
    co
    #
    cC
    cmin
    co
    #
    @4
    cA
    cC
    caddc
    co
    cmin
    co
    #
    cB
    cC
    cmin
    co
    @3
    @4
    cc
    wcel
    @0
    @2
    @6
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
    subsub4
    syl3anc
    @3
    @5
    cB
    cC
    cmin
    @0
    @1
    @5
    cB
    wceq
    @2
    cA
    cB
    pncan2
    3adant3
    oveq1d
    eqtr3d
end
