include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "cgcd.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "gcdcom.mm"
include "oveq2d.mm"
include "3adant1.mm"
include "gcdass.mm"
include "3com23.mm"
include "3eqtr4d.mm"

theorem gcd32
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. ZZ /\ B e. ZZ /\ C e. ZZ ) -> ( ( A gcd B ) gcd C ) = ( ( A gcd C ) gcd B ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    cC
    cz
    wcel
    #
    w3a
    cA
    cB
    cC
    cgcd
    co
    #
    cgcd
    co
    #
    cA
    cC
    cB
    cgcd
    co
    #
    cgcd
    co
    #
    cA
    cB
    cgcd
    co
    cC
    cgcd
    co
    cA
    cC
    cgcd
    co
    cB
    cgcd
    co
    #
    @1
    @2
    @4
    @6
    wceq
    @0
    @1
    @2
    wa
    @3
    @5
    cA
    cgcd
    cB
    cC
    gcdcom
    oveq2d
    3adant1
    cC
    cB
    cA
    gcdass
    @0
    @2
    @1
    @7
    @6
    wceq
    cB
    cC
    cA
    gcdass
    3com23
    3eqtr4d
end
