include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "simp1.mm"
include "wa.mm"
include "simpr.mm"
include "simpl.mm"
include "subcld.mm"
include "3adant1.mm"
include "addcomd.mm"
include "subsub2.mm"
include "simp3.mm"
include "simp2.mm"
include "subsubd.mm"
include "3eqtr4d.mm"

theorem sub31
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( A - ( B - C ) ) = ( C - ( B - A ) ) )

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
    cC
    cB
    cmin
    co
    #
    caddc
    co
    @4
    cA
    caddc
    co
    cA
    cB
    cC
    cmin
    co
    cmin
    co
    cC
    cB
    cA
    cmin
    co
    cmin
    co
    @3
    cA
    @4
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
    @1
    @2
    wa
    cC
    cB
    @1
    @2
    simpr
    @1
    @2
    simpl
    subcld
    3adant1
    addcomd
    cA
    cB
    cC
    subsub2
    @3
    cC
    cB
    cA
    @0
    @1
    @2
    simp3
    @0
    @1
    @2
    simp2
    @5
    subsubd
    3eqtr4d
end
