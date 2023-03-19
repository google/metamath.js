include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "cgcd.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "wceq.mm"
include "0z.mm"
include "gcdcom.mm"
include "mpan.mm"
include "gcd0id.mm"
include "eqtr3d.mm"

theorem gcdid0
  let cN: class N


  assert |- ( N e. ZZ -> ( N gcd 0 ) = ( abs ` N ) )

  proof
    cN
    cz
    wcel
    #
    cc0
    cN
    cgcd
    co
    #
    cN
    cc0
    cgcd
    co
    #
    cN
    cabs
    cfv
    cc0
    cz
    wcel
    @0
    @1
    @2
    wceq
    0z
    cc0
    cN
    gcdcom
    mpan
    cN
    gcd0id
    eqtr3d
end
