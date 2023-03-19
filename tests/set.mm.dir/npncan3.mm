include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "simp1.mm"
include "subcl.mm"
include "ancoms.mm"
include "3adant2.mm"
include "simp2.mm"
include "addsub.mm"
include "syl3anc.mm"
include "pncan3.mm"
include "oveq1d.mm"
include "eqtr3d.mm"

theorem npncan3
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( A - B ) + ( C - A ) ) = ( C - B ) )

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
    cA
    cmin
    co
    #
    caddc
    co
    #
    cB
    cmin
    co
    #
    cA
    cB
    cmin
    co
    @4
    caddc
    co
    #
    cC
    cB
    cmin
    co
    @3
    @0
    @4
    cc
    wcel
    #
    @1
    @6
    @7
    wceq
    @0
    @1
    @2
    simp1
    @0
    @2
    @8
    @1
    @2
    @0
    @8
    cC
    cA
    subcl
    ancoms
    3adant2
    @0
    @1
    @2
    simp2
    cA
    @4
    cB
    addsub
    syl3anc
    @3
    @5
    cC
    cB
    cmin
    @0
    @2
    @5
    cC
    wceq
    @1
    cA
    cC
    pncan3
    3adant2
    oveq1d
    eqtr3d
end
