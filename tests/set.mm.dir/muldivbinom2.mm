include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "c2.mm"
include "cexp.mm"
include "cmin.mm"
include "cdiv.mm"
include "wceq.mm"
include "simpl.mm"
include "simpr.mm"
include "0cnd.mm"
include "3jca.mm"
include "mulsubdivbinom2.mm"
include "stoic3.mm"
include "simp3l.mm"
include "simp1.mm"
include "mulcld.mm"
include "simp2.mm"
include "addcld.mm"
include "sqcld.mm"
include "subid1d.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "sqcl.mm"
include "3ad2ant2.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"

theorem muldivbinom2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ ( C e. CC /\ C =/= 0 ) ) -> ( ( ( ( C x. A ) + B ) ^ 2 ) / C ) = ( ( ( C x. ( A ^ 2 ) ) + ( 2 x. ( A x. B ) ) ) + ( ( B ^ 2 ) / C ) ) )

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
    cC
    cc0
    wne
    #
    wa
    #
    w3a
    #
    cC
    cA
    cmul
    co
    #
    cB
    caddc
    co
    #
    c2
    cexp
    co
    #
    cc0
    cmin
    co
    #
    cC
    cdiv
    co
    #
    cC
    cA
    c2
    cexp
    co
    cmul
    co
    c2
    cA
    cB
    cmul
    co
    cmul
    co
    caddc
    co
    #
    cB
    c2
    cexp
    co
    #
    cc0
    cmin
    co
    #
    cC
    cdiv
    co
    #
    caddc
    co
    #
    @8
    cC
    cdiv
    co
    @11
    @12
    cC
    cdiv
    co
    #
    caddc
    co
    @0
    @1
    @0
    @1
    cc0
    cc
    wcel
    #
    w3a
    @4
    @10
    @15
    wceq
    @0
    @1
    wa
    #
    @0
    @1
    @17
    @0
    @1
    simpl
    @0
    @1
    simpr
    @18
    0cnd
    3jca
    cA
    cB
    cC
    cc0
    mulsubdivbinom2
    stoic3
    @5
    @8
    @9
    cC
    cdiv
    @5
    @9
    @8
    @5
    @8
    @5
    @7
    @5
    @6
    cB
    @5
    cC
    cA
    @0
    @1
    @2
    @3
    simp3l
    @0
    @1
    @4
    simp1
    mulcld
    @0
    @1
    @4
    simp2
    addcld
    sqcld
    subid1d
    eqcomd
    oveq1d
    @5
    @16
    @14
    @11
    caddc
    @5
    @12
    @13
    cC
    cdiv
    @5
    @13
    @12
    @1
    @0
    @13
    @12
    wceq
    @4
    @1
    @12
    cB
    sqcl
    subid1d
    3ad2ant2
    eqcomd
    oveq1d
    oveq2d
    3eqtr4d
end
