include "cxr.mm"
include "wcel.mm"
include "c1.mm"
include "cxmu.mm"
include "co.mm"
include "wceq.mm"
include "1re.mm"
include "rexri.mm"
include "xmulcom.mm"
include "mpan.mm"
include "xmulid1.mm"
include "eqtrd.mm"

theorem xmulid2
  let cA: class A


  assert |- ( A e. RR* -> ( 1 *e A ) = A )

  proof
    cA
    cxr
    wcel
    #
    c1
    cA
    cxmu
    co
    #
    cA
    c1
    cxmu
    co
    #
    cA
    c1
    cxr
    wcel
    @0
    @1
    @2
    wceq
    c1
    1re
    rexri
    c1
    cA
    xmulcom
    mpan
    cA
    xmulid1
    eqtrd
end
