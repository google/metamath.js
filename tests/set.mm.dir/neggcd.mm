include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cneg.mm"
include "cgcd.mm"
include "co.mm"
include "wceq.mm"
include "gcdneg.mm"
include "ancoms.mm"
include "znegcl.mm"
include "gcdcom.mm"
include "sylan.mm"
include "3eqtr4d.mm"

theorem neggcd
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( -u M gcd N ) = ( M gcd N ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    cN
    cM
    cneg
    #
    cgcd
    co
    #
    cN
    cM
    cgcd
    co
    #
    @2
    cN
    cgcd
    co
    #
    cM
    cN
    cgcd
    co
    @1
    @0
    @3
    @4
    wceq
    cN
    cM
    gcdneg
    ancoms
    @0
    @2
    cz
    wcel
    @1
    @5
    @3
    wceq
    cM
    znegcl
    @2
    cN
    gcdcom
    sylan
    cM
    cN
    gcdcom
    3eqtr4d
end
