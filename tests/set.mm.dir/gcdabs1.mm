include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cabs.mm"
include "cfv.mm"
include "wceq.mm"
include "cgcd.mm"
include "co.mm"
include "cneg.mm"
include "wi.mm"
include "oveq1.mm"
include "a1i.mm"
include "neggcd.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "wo.mm"
include "zre.mm"
include "absord.mm"
include "adantr.mm"
include "mpjaod.mm"

theorem gcdabs1
  let cM: class M
  let cN: class N


  assert |- ( ( N e. ZZ /\ M e. ZZ ) -> ( ( abs ` N ) gcd M ) = ( N gcd M ) )

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
    #
    cN
    cabs
    cfv
    #
    cN
    wceq
    #
    @3
    cM
    cgcd
    co
    #
    cN
    cM
    cgcd
    co
    #
    wceq
    #
    @3
    cN
    cneg
    #
    wceq
    #
    @4
    @7
    wi
    @2
    @3
    cN
    cM
    cgcd
    oveq1
    a1i
    @2
    @7
    @9
    @8
    cM
    cgcd
    co
    #
    @6
    wceq
    cN
    cM
    neggcd
    @9
    @5
    @10
    @6
    @3
    @8
    cM
    cgcd
    oveq1
    eqeq1d
    syl5ibrcom
    @0
    @4
    @9
    wo
    @1
    @0
    cN
    cN
    zre
    absord
    adantr
    mpjaod
end
