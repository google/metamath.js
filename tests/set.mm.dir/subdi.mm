include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "cmin.mm"
include "wceq.mm"
include "caddc.mm"
include "simp1.mm"
include "simp3.mm"
include "subcl.mm"
include "3adant1.mm"
include "adddid.mm"
include "pncan3.mm"
include "ancoms.mm"
include "oveq2d.mm"
include "eqtr3d.mm"
include "mulcl.mm"
include "3adant3.mm"
include "3adant2.mm"
include "wa.mm"
include "sylan2.mm"
include "3impb.mm"
include "subaddd.mm"
include "mpbird.mm"
include "eqcomd.mm"

theorem subdi
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( A x. ( B - C ) ) = ( ( A x. B ) - ( A x. C ) ) )

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
    cmul
    co
    #
    cA
    cC
    cmul
    co
    #
    cmin
    co
    #
    cA
    cB
    cC
    cmin
    co
    #
    cmul
    co
    #
    @3
    @6
    @8
    wceq
    @5
    @8
    caddc
    co
    #
    @4
    wceq
    @3
    cA
    cC
    @7
    caddc
    co
    #
    cmul
    co
    @9
    @4
    @3
    cA
    cC
    @7
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp3
    @1
    @2
    @7
    cc
    wcel
    #
    @0
    cB
    cC
    subcl
    #
    3adant1
    adddid
    @3
    @10
    cB
    cA
    cmul
    @1
    @2
    @10
    cB
    wceq
    #
    @0
    @2
    @1
    @13
    cC
    cB
    pncan3
    ancoms
    3adant1
    oveq2d
    eqtr3d
    @3
    @4
    @5
    @8
    @0
    @1
    @4
    cc
    wcel
    @2
    cA
    cB
    mulcl
    3adant3
    @0
    @2
    @5
    cc
    wcel
    @1
    cA
    cC
    mulcl
    3adant2
    @0
    @1
    @2
    @8
    cc
    wcel
    #
    @1
    @2
    wa
    @0
    @11
    @14
    @12
    cA
    @7
    mulcl
    sylan2
    3impb
    subaddd
    mpbird
    eqcomd
end
