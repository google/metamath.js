include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "simp1.mm"
include "subcl.mm"
include "3adant1.mm"
include "simp3.mm"
include "addassd.mm"
include "wceq.mm"
include "npcan.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "addcld.mm"
include "pncan.mm"
include "syl2anc.mm"
include "eqtr3d.mm"

theorem addsubass
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( A + B ) - C ) = ( A + ( B - C ) ) )

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
    cmin
    co
    #
    caddc
    co
    #
    cC
    caddc
    co
    #
    cC
    cmin
    co
    #
    cA
    cB
    caddc
    co
    #
    cC
    cmin
    co
    @5
    @3
    @6
    @8
    cC
    cmin
    @3
    @6
    cA
    @4
    cC
    caddc
    co
    #
    caddc
    co
    @8
    @3
    cA
    @4
    cC
    @0
    @1
    @2
    simp1
    #
    @1
    @2
    @4
    cc
    wcel
    @0
    cB
    cC
    subcl
    3adant1
    #
    @0
    @1
    @2
    simp3
    #
    addassd
    @3
    @9
    cB
    cA
    caddc
    @1
    @2
    @9
    cB
    wceq
    @0
    cB
    cC
    npcan
    3adant1
    oveq2d
    eqtrd
    oveq1d
    @3
    @5
    cc
    wcel
    @2
    @7
    @5
    wceq
    @3
    cA
    @4
    @10
    @11
    addcld
    @12
    @5
    cC
    pncan
    syl2anc
    eqtr3d
end
