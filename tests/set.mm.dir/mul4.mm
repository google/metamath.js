include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "mul32.mm"
include "oveq1d.mm"
include "3expa.mm"
include "adantrr.mm"
include "mulcl.mm"
include "mulass.mm"
include "3expb.mm"
include "sylan.mm"
include "an4s.mm"
include "3eqtr3d.mm"

theorem mul4
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. CC /\ B e. CC ) /\ ( C e. CC /\ D e. CC ) ) -> ( ( A x. B ) x. ( C x. D ) ) = ( ( A x. C ) x. ( B x. D ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    cC
    cc
    wcel
    #
    cD
    cc
    wcel
    #
    wa
    #
    wa
    cA
    cB
    cmul
    co
    #
    cC
    cmul
    co
    #
    cD
    cmul
    co
    #
    cA
    cC
    cmul
    co
    #
    cB
    cmul
    co
    #
    cD
    cmul
    co
    #
    @6
    cC
    cD
    cmul
    co
    cmul
    co
    #
    @9
    cB
    cD
    cmul
    co
    cmul
    co
    #
    @2
    @3
    @8
    @11
    wceq
    #
    @4
    @0
    @1
    @3
    @14
    @0
    @1
    @3
    w3a
    @7
    @10
    cD
    cmul
    cA
    cB
    cC
    mul32
    oveq1d
    3expa
    adantrr
    @2
    @6
    cc
    wcel
    #
    @5
    @8
    @12
    wceq
    #
    cA
    cB
    mulcl
    @15
    @3
    @4
    @16
    @6
    cC
    cD
    mulass
    3expb
    sylan
    @0
    @3
    @1
    @4
    @11
    @13
    wceq
    #
    @0
    @3
    wa
    @9
    cc
    wcel
    #
    @1
    @4
    wa
    @17
    cA
    cC
    mulcl
    @18
    @1
    @4
    @17
    @9
    cB
    cD
    mulass
    3expb
    sylan
    an4s
    3eqtr3d
end
