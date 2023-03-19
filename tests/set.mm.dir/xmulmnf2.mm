include "cxr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cmnf.mm"
include "cxmu.mm"
include "co.mm"
include "wceq.mm"
include "mnfxr.mm"
include "xmulcom.mm"
include "mpan.mm"
include "adantr.mm"
include "xmulmnf1.mm"
include "eqtrd.mm"

theorem xmulmnf2
  let cA: class A


  assert |- ( ( A e. RR* /\ 0 < A ) -> ( -oo *e A ) = -oo )

  proof
    cA
    cxr
    wcel
    #
    cc0
    cA
    clt
    wbr
    #
    wa
    cmnf
    cA
    cxmu
    co
    #
    cA
    cmnf
    cxmu
    co
    #
    cmnf
    @0
    @2
    @3
    wceq
    #
    @1
    cmnf
    cxr
    wcel
    @0
    @4
    mnfxr
    cmnf
    cA
    xmulcom
    mpan
    adantr
    cA
    xmulmnf1
    eqtrd
end
