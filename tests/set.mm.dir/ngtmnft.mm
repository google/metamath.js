include "cxr.mm"
include "wcel.mm"
include "cmnf.mm"
include "wceq.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "mnfxr.mm"
include "xrltnr.mm"
include "ax-mp.mm"
include "breq2.mm"
include "mtbiri.mm"
include "cle.mm"
include "wo.mm"
include "mnfle.mm"
include "wb.mm"
include "xrleloe.mm"
include "mpan.mm"
include "mpbid.mm"
include "ord.mm"
include "eqcom.mm"
include "syl6ib.mm"
include "impbid2.mm"

theorem ngtmnft
  let cA: class A


  assert |- ( A e. RR* -> ( A = -oo <-> -. -oo < A ) )

  proof
    cA
    cxr
    wcel
    #
    cA
    cmnf
    wceq
    #
    cmnf
    cA
    clt
    wbr
    #
    wn
    #
    @1
    @2
    cmnf
    cmnf
    clt
    wbr
    #
    cmnf
    cxr
    wcel
    #
    @4
    wn
    mnfxr
    cmnf
    xrltnr
    ax-mp
    cA
    cmnf
    cmnf
    clt
    breq2
    mtbiri
    @0
    @3
    cmnf
    cA
    wceq
    #
    @1
    @0
    @2
    @6
    @0
    cmnf
    cA
    cle
    wbr
    #
    @2
    @6
    wo
    #
    cA
    mnfle
    @5
    @0
    @7
    @8
    wb
    mnfxr
    cmnf
    cA
    xrleloe
    mpan
    mpbid
    ord
    cmnf
    cA
    eqcom
    syl6ib
    impbid2
end
