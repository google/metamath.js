include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "nppcan2.mm"
include "wb.mm"
include "simp1.mm"
include "simp2.mm"
include "subcl.mm"
include "syl2anc.mm"
include "simp3.mm"
include "addcld.mm"
include "subadd2.mm"
include "syl3anc.mm"
include "mpbird.mm"

theorem subsub4
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( A - B ) - C ) = ( A - ( B + C ) ) )

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
    cA
    cB
    cC
    caddc
    co
    #
    cmin
    co
    #
    wceq
    #
    @6
    cC
    caddc
    co
    @4
    wceq
    #
    cA
    cB
    cC
    nppcan2
    @3
    @4
    cc
    wcel
    #
    @2
    @6
    cc
    wcel
    #
    @7
    @8
    wb
    @3
    @0
    @1
    @9
    @0
    @1
    @2
    simp1
    #
    @0
    @1
    @2
    simp2
    #
    cA
    cB
    subcl
    syl2anc
    @0
    @1
    @2
    simp3
    #
    @3
    @0
    @5
    cc
    wcel
    @10
    @11
    @3
    cB
    cC
    @12
    @13
    addcld
    cA
    @5
    subcl
    syl2anc
    @4
    cC
    @6
    subadd2
    syl3anc
    mpbird
end
