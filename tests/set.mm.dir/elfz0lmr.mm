include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "wceq.mm"
include "c1.mm"
include "caddc.mm"
include "cfzo.mm"
include "w3o.mm"
include "elfzlmr.mm"
include "biid.mm"
include "0p1e1.mm"
include "oveq1i.mm"
include "eleq2i.mm"
include "3orbi123i.mm"
include "sylib.mm"

theorem elfz0lmr
  let cK: class K
  let cN: class N


  assert |- ( K e. ( 0 ... N ) -> ( K = 0 \/ K e. ( 1 ..^ N ) \/ K = N ) )

  proof
    cK
    cc0
    cN
    cfz
    co
    wcel
    cK
    cc0
    wceq
    #
    cK
    cc0
    c1
    caddc
    co
    #
    cN
    cfzo
    co
    #
    wcel
    #
    cK
    cN
    wceq
    #
    w3o
    @0
    cK
    c1
    cN
    cfzo
    co
    #
    wcel
    #
    @4
    w3o
    cK
    cc0
    cN
    elfzlmr
    @0
    @0
    @3
    @6
    @4
    @4
    @0
    biid
    @2
    @5
    cK
    @1
    c1
    cN
    cfzo
    0p1e1
    oveq1i
    eleq2i
    @4
    biid
    3orbi123i
    sylib
end
