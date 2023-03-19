include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "clt.mm"
include "hashge0.mm"
include "adantr.mm"
include "hasheq0.mm"
include "necon3bid.mm"
include "biimpar.mm"
include "jca.mm"
include "cxr.mm"
include "wb.mm"
include "0xr.mm"
include "hashxrcl.mm"
include "xrltlen.mm"
include "sylancr.mm"
include "syldan.mm"

theorem hashgt0
  let cA: class A
  let cV: class V


  assert |- ( ( A e. V /\ A =/= (/) ) -> 0 < ( # ` A ) )

  proof
    cA
    cV
    wcel
    #
    cA
    c0
    wne
    #
    cc0
    cA
    chash
    cfv
    #
    cle
    wbr
    #
    @2
    cc0
    wne
    #
    wa
    #
    cc0
    @2
    clt
    wbr
    #
    @0
    @1
    wa
    @3
    @4
    @0
    @3
    @1
    cA
    cV
    hashge0
    adantr
    @0
    @4
    @1
    @0
    @2
    cc0
    cA
    c0
    cA
    cV
    hasheq0
    necon3bid
    biimpar
    jca
    @0
    @6
    @5
    @0
    cc0
    cxr
    wcel
    @2
    cxr
    wcel
    @6
    @5
    wb
    0xr
    cA
    cV
    hashxrcl
    cc0
    @2
    xrltlen
    sylancr
    biimpar
    syldan
end
