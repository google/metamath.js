include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cgcd.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "wceq.mm"
include "gcdass.mm"
include "3anidm23.mm"
include "gcdid.mm"
include "oveq2d.mm"
include "adantl.mm"
include "gcdabs2.mm"
include "3eqtrd.mm"

theorem gcdabsorb
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ZZ /\ B e. ZZ ) -> ( ( A gcd B ) gcd B ) = ( A gcd B ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    wa
    cA
    cB
    cgcd
    co
    #
    cB
    cgcd
    co
    #
    cA
    cB
    cB
    cgcd
    co
    #
    cgcd
    co
    #
    cA
    cB
    cabs
    cfv
    #
    cgcd
    co
    #
    @2
    @0
    @1
    @3
    @5
    wceq
    cB
    cB
    cA
    gcdass
    3anidm23
    @1
    @5
    @7
    wceq
    @0
    @1
    @4
    @6
    cA
    cgcd
    cB
    gcdid
    oveq2d
    adantl
    cB
    cA
    gcdabs2
    3eqtrd
end
