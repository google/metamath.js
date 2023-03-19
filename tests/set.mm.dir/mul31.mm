include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "mulcom.mm"
include "oveq2d.mm"
include "3adant1.mm"
include "mulass.mm"
include "mulcl.mm"
include "ancoms.mm"
include "simp1.mm"
include "mulcomd.mm"
include "3eqtr4d.mm"

theorem mul31
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( A x. B ) x. C ) = ( ( C x. B ) x. A ) )

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
    cmul
    co
    #
    cmul
    co
    #
    cA
    cC
    cB
    cmul
    co
    #
    cmul
    co
    #
    cA
    cB
    cmul
    co
    cC
    cmul
    co
    @6
    cA
    cmul
    co
    @1
    @2
    @5
    @7
    wceq
    @0
    @1
    @2
    wa
    @4
    @6
    cA
    cmul
    cB
    cC
    mulcom
    oveq2d
    3adant1
    cA
    cB
    cC
    mulass
    @3
    @6
    cA
    @1
    @2
    @6
    cc
    wcel
    #
    @0
    @2
    @1
    @8
    cC
    cB
    mulcl
    ancoms
    3adant1
    @0
    @1
    @2
    simp1
    mulcomd
    3eqtr4d
end
