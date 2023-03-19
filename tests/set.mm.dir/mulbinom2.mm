include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "c2.mm"
include "cexp.mm"
include "wceq.mm"
include "mulcl.mm"
include "ancoms.mm"
include "3adant2.mm"
include "simp2.mm"
include "binom2.mm"
include "syl2anc.mm"
include "mulass.mm"
include "3coml.mm"
include "oveq2d.mm"
include "2cnd.mm"
include "simp3.mm"
include "3adant3.mm"
include "mulassd.mm"
include "eqtr4d.mm"
include "oveq1d.mm"
include "eqtrd.mm"

theorem mulbinom2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( ( C x. A ) + B ) ^ 2 ) = ( ( ( ( C x. A ) ^ 2 ) + ( ( 2 x. C ) x. ( A x. B ) ) ) + ( B ^ 2 ) ) )

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
    cC
    cA
    cmul
    co
    #
    cB
    caddc
    co
    c2
    cexp
    co
    #
    @4
    c2
    cexp
    co
    #
    c2
    @4
    cB
    cmul
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    cB
    c2
    cexp
    co
    #
    caddc
    co
    #
    @6
    c2
    cC
    cmul
    co
    cA
    cB
    cmul
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    @10
    caddc
    co
    @3
    @4
    cc
    wcel
    #
    @1
    @5
    @11
    wceq
    @0
    @2
    @15
    @1
    @2
    @0
    @15
    cC
    cA
    mulcl
    ancoms
    3adant2
    @0
    @1
    @2
    simp2
    @4
    cB
    binom2
    syl2anc
    @3
    @9
    @14
    @10
    caddc
    @3
    @8
    @13
    @6
    caddc
    @3
    @8
    c2
    cC
    @12
    cmul
    co
    #
    cmul
    co
    @13
    @3
    @7
    @16
    c2
    cmul
    @2
    @0
    @1
    @7
    @16
    wceq
    cC
    cA
    cB
    mulass
    3coml
    oveq2d
    @3
    c2
    cC
    @12
    @3
    2cnd
    @0
    @1
    @2
    simp3
    @0
    @1
    @12
    cc
    wcel
    @2
    cA
    cB
    mulcl
    3adant3
    mulassd
    eqtr4d
    oveq2d
    oveq1d
    eqtrd
end
