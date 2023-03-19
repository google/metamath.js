include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "subcl.mm"
include "3adant3.mm"
include "simp3.mm"
include "simp1.mm"
include "addsubd.mm"
include "wceq.mm"
include "wa.mm"
include "simpl.mm"
include "simpr.mm"
include "3jca.mm"
include "sub32.mm"
include "syl.mm"
include "oveq1d.mm"
include "cc0.mm"
include "anidms.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "subadd23d.mm"
include "subid.mm"
include "ancoms.mm"
include "addid2d.mm"
include "3adant1.mm"
include "3eqtrd.mm"

theorem cnambpcma
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( ( A - B ) + C ) - A ) = ( C - B ) )

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
    caddc
    co
    cA
    cmin
    co
    @4
    cA
    cmin
    co
    #
    cC
    caddc
    co
    cA
    cA
    cmin
    co
    #
    cB
    cmin
    co
    #
    cC
    caddc
    co
    #
    cC
    cB
    cmin
    co
    #
    @3
    @4
    cC
    cA
    @0
    @1
    @4
    cc
    wcel
    @2
    cA
    cB
    subcl
    3adant3
    @0
    @1
    @2
    simp3
    #
    @0
    @1
    @2
    simp1
    addsubd
    @3
    @5
    @7
    cC
    caddc
    @3
    @0
    @1
    @0
    w3a
    #
    @5
    @7
    wceq
    @0
    @1
    @11
    @2
    @0
    @1
    wa
    @0
    @1
    @0
    @0
    @1
    simpl
    #
    @0
    @1
    simpr
    @12
    3jca
    3adant3
    cA
    cB
    cA
    sub32
    syl
    oveq1d
    @3
    @8
    @6
    @9
    caddc
    co
    #
    cc0
    @9
    caddc
    co
    #
    @9
    @3
    @6
    cB
    cC
    @0
    @1
    @6
    cc
    wcel
    #
    @2
    @0
    @15
    cA
    cA
    subcl
    anidms
    3ad2ant1
    @0
    @1
    @2
    simp2
    @10
    subadd23d
    @0
    @1
    @13
    @14
    wceq
    @2
    @0
    @6
    cc0
    @9
    caddc
    cA
    subid
    oveq1d
    3ad2ant1
    @1
    @2
    @14
    @9
    wceq
    @0
    @1
    @2
    wa
    @9
    @2
    @1
    @9
    cc
    wcel
    cC
    cB
    subcl
    ancoms
    addid2d
    3adant1
    3eqtrd
    3eqtrd
end
