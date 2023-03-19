include "cxr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cpnf.mm"
include "cxmu.mm"
include "co.mm"
include "wceq.mm"
include "pnfxr.mm"
include "xmulcom.mm"
include "mpan.mm"
include "adantr.mm"
include "xmulpnf1.mm"
include "eqtrd.mm"

theorem xmulpnf2
  let cA: class A


  assert |- ( ( A e. RR* /\ 0 < A ) -> ( +oo *e A ) = +oo )

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
    cpnf
    cA
    cxmu
    co
    #
    cA
    cpnf
    cxmu
    co
    #
    cpnf
    @0
    @2
    @3
    wceq
    #
    @1
    cpnf
    cxr
    wcel
    @0
    @4
    pnfxr
    cpnf
    cA
    xmulcom
    mpan
    adantr
    cA
    xmulpnf1
    eqtrd
end
