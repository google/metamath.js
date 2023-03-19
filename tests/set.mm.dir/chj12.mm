include "cch.mm"
include "wcel.mm"
include "w3a.mm"
include "chj.mm"
include "co.mm"
include "wceq.mm"
include "chjcom.mm"
include "3adant3.mm"
include "oveq1d.mm"
include "chjass.mm"
include "3com12.mm"
include "3eqtr3d.mm"

theorem chj12
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CH /\ B e. CH /\ C e. CH ) -> ( A vH ( B vH C ) ) = ( B vH ( A vH C ) ) )

  proof
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    cC
    cch
    wcel
    #
    w3a
    #
    cA
    cB
    chj
    co
    #
    cC
    chj
    co
    cB
    cA
    chj
    co
    #
    cC
    chj
    co
    #
    cA
    cB
    cC
    chj
    co
    chj
    co
    cB
    cA
    cC
    chj
    co
    chj
    co
    #
    @3
    @4
    @5
    cC
    chj
    @0
    @1
    @4
    @5
    wceq
    @2
    cA
    cB
    chjcom
    3adant3
    oveq1d
    cA
    cB
    cC
    chjass
    @1
    @0
    @2
    @6
    @7
    wceq
    cB
    cA
    cC
    chjass
    3com12
    3eqtr3d
end
