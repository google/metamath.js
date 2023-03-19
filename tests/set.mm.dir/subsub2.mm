include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "cc0.mm"
include "subcl.mm"
include "3adant1.mm"
include "simp1.mm"
include "simp3.mm"
include "simp2.mm"
include "syl2anc.mm"
include "add12d.mm"
include "npncan2.mm"
include "oveq2d.mm"
include "addid1d.mm"
include "3eqtrd.mm"
include "wb.mm"
include "addcld.mm"
include "subadd.mm"
include "syl3anc.mm"
include "mpbird.mm"

theorem subsub2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( A - ( B - C ) ) = ( A + ( C - B ) ) )

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
    cmin
    co
    cA
    cC
    cB
    cmin
    co
    #
    caddc
    co
    #
    wceq
    #
    @4
    @6
    caddc
    co
    #
    cA
    wceq
    #
    @3
    @8
    cA
    @4
    @5
    caddc
    co
    #
    caddc
    co
    cA
    cc0
    caddc
    co
    cA
    @3
    @4
    cA
    @5
    @1
    @2
    @4
    cc
    wcel
    #
    @0
    cB
    cC
    subcl
    3adant1
    #
    @0
    @1
    @2
    simp1
    #
    @3
    @2
    @1
    @5
    cc
    wcel
    @0
    @1
    @2
    simp3
    @0
    @1
    @2
    simp2
    cC
    cB
    subcl
    syl2anc
    #
    add12d
    @3
    @10
    cc0
    cA
    caddc
    @1
    @2
    @10
    cc0
    wceq
    @0
    cB
    cC
    npncan2
    3adant1
    oveq2d
    @3
    cA
    @13
    addid1d
    3eqtrd
    @3
    @0
    @11
    @6
    cc
    wcel
    @7
    @9
    wb
    @13
    @12
    @3
    cA
    @5
    @13
    @14
    addcld
    cA
    @4
    @6
    subadd
    syl3anc
    mpbird
end
