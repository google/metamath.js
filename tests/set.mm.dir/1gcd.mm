include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "cgcd.mm"
include "co.mm"
include "wceq.mm"
include "1z.mm"
include "gcdcom.mm"
include "mpan.mm"
include "gcd1.mm"
include "eqtrd.mm"

theorem 1gcd
  let cM: class M


  assert |- ( M e. ZZ -> ( 1 gcd M ) = 1 )

  proof
    cM
    cz
    wcel
    #
    c1
    cM
    cgcd
    co
    #
    cM
    c1
    cgcd
    co
    #
    c1
    c1
    cz
    wcel
    @0
    @1
    @2
    wceq
    1z
    c1
    cM
    gcdcom
    mpan
    cM
    gcd1
    eqtrd
end
