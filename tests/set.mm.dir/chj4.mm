include "cch.mm"
include "wcel.mm"
include "wa.mm"
include "chj.mm"
include "co.mm"
include "wceq.mm"
include "chj12.mm"
include "3expb.mm"
include "adantll.mm"
include "oveq2d.mm"
include "chjcl.mm"
include "chjass.mm"
include "3expa.mm"
include "sylan2.mm"
include "an4s.mm"
include "3eqtr4d.mm"

theorem chj4
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. CH /\ B e. CH ) /\ ( C e. CH /\ D e. CH ) ) -> ( ( A vH B ) vH ( C vH D ) ) = ( ( A vH C ) vH ( B vH D ) ) )

  proof
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    wa
    #
    cC
    cch
    wcel
    #
    cD
    cch
    wcel
    #
    wa
    #
    wa
    #
    cA
    cB
    cC
    cD
    chj
    co
    #
    chj
    co
    #
    chj
    co
    #
    cA
    cC
    cB
    cD
    chj
    co
    #
    chj
    co
    #
    chj
    co
    #
    cA
    cB
    chj
    co
    @7
    chj
    co
    #
    cA
    cC
    chj
    co
    @10
    chj
    co
    #
    @6
    @8
    @11
    cA
    chj
    @1
    @5
    @8
    @11
    wceq
    #
    @0
    @1
    @3
    @4
    @15
    cB
    cC
    cD
    chj12
    3expb
    adantll
    oveq2d
    @5
    @2
    @7
    cch
    wcel
    #
    @13
    @9
    wceq
    #
    cC
    cD
    chjcl
    @0
    @1
    @16
    @17
    cA
    cB
    @7
    chjass
    3expa
    sylan2
    @0
    @3
    @1
    @4
    @14
    @12
    wceq
    #
    @1
    @4
    wa
    @0
    @3
    wa
    @10
    cch
    wcel
    #
    @18
    cB
    cD
    chjcl
    @0
    @3
    @19
    @18
    cA
    cC
    @10
    chjass
    3expa
    sylan2
    an4s
    3eqtr4d
end
