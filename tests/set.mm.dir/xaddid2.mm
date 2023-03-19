include "cxr.mm"
include "wcel.mm"
include "cc0.mm"
include "cxad.mm"
include "co.mm"
include "wceq.mm"
include "0xr.mm"
include "xaddcom.mm"
include "mpan.mm"
include "xaddid1.mm"
include "eqtrd.mm"

theorem xaddid2
  let cA: class A


  assert |- ( A e. RR* -> ( 0 +e A ) = A )

  proof
    cA
    cxr
    wcel
    #
    cc0
    cA
    cxad
    co
    #
    cA
    cc0
    cxad
    co
    #
    cA
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
    xaddcom
    mpan
    cA
    xaddid1
    eqtrd
end
