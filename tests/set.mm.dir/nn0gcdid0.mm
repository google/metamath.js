include "cn0.mm"
include "wcel.mm"
include "cc0.mm"
include "cgcd.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "cz.mm"
include "wceq.mm"
include "nn0z.mm"
include "gcdid0.mm"
include "syl.mm"
include "nn0re.mm"
include "nn0ge0.mm"
include "absidd.mm"
include "eqtrd.mm"

theorem nn0gcdid0
  let cN: class N


  assert |- ( N e. NN0 -> ( N gcd 0 ) = N )

  proof
    cN
    cn0
    wcel
    #
    cN
    cc0
    cgcd
    co
    #
    cN
    cabs
    cfv
    #
    cN
    @0
    cN
    cz
    wcel
    @1
    @2
    wceq
    cN
    nn0z
    cN
    gcdid0
    syl
    @0
    cN
    cN
    nn0re
    cN
    nn0ge0
    absidd
    eqtrd
end
