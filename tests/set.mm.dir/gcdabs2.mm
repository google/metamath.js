include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cabs.mm"
include "cfv.mm"
include "cgcd.mm"
include "co.mm"
include "wceq.mm"
include "gcdabs1.mm"
include "ancoms.mm"
include "zabscl.mm"
include "gcdcom.mm"
include "sylan2.mm"
include "3eqtr4d.mm"

theorem gcdabs2
  let cM: class M
  let cN: class N


  assert |- ( ( N e. ZZ /\ M e. ZZ ) -> ( N gcd ( abs ` M ) ) = ( N gcd M ) )

  proof
    cN
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    wa
    cM
    cabs
    cfv
    #
    cN
    cgcd
    co
    #
    cM
    cN
    cgcd
    co
    #
    cN
    @2
    cgcd
    co
    #
    cN
    cM
    cgcd
    co
    @1
    @0
    @3
    @4
    wceq
    cN
    cM
    gcdabs1
    ancoms
    @1
    @0
    @2
    cz
    wcel
    @5
    @3
    wceq
    cM
    zabscl
    cN
    @2
    gcdcom
    sylan2
    cN
    cM
    gcdcom
    3eqtr4d
end
