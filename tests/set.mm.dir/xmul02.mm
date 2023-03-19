include "cxr.mm"
include "wcel.mm"
include "cc0.mm"
include "cxmu.mm"
include "co.mm"
include "wceq.mm"
include "0xr.mm"
include "xmulcom.mm"
include "mpan.mm"
include "xmul01.mm"
include "eqtrd.mm"

theorem xmul02
  let cA: class A


  assert |- ( A e. RR* -> ( 0 *e A ) = 0 )

  proof
    cA
    cxr
    wcel
    #
    cc0
    cA
    cxmu
    co
    #
    cA
    cc0
    cxmu
    co
    #
    cc0
    cc0
    cxr
    wcel
    @0
    @1
    @2
    wceq
    0xr
    cc0
    cA
    xmulcom
    mpan
    cA
    xmul01
    eqtrd
end
