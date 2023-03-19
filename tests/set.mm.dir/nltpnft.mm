include "cxr.mm"
include "wcel.mm"
include "cpnf.mm"
include "wceq.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "pnfxr.mm"
include "xrltnr.mm"
include "ax-mp.mm"
include "breq1.mm"
include "mtbiri.mm"
include "cle.mm"
include "wo.mm"
include "pnfge.mm"
include "wb.mm"
include "xrleloe.mm"
include "mpan2.mm"
include "mpbid.mm"
include "ord.mm"
include "impbid2.mm"

theorem nltpnft
  let cA: class A


  assert |- ( A e. RR* -> ( A = +oo <-> -. A < +oo ) )

  proof
    cA
    cxr
    wcel
    #
    cA
    cpnf
    wceq
    #
    cA
    cpnf
    clt
    wbr
    #
    wn
    @1
    @2
    cpnf
    cpnf
    clt
    wbr
    #
    cpnf
    cxr
    wcel
    #
    @3
    wn
    pnfxr
    cpnf
    xrltnr
    ax-mp
    cA
    cpnf
    cpnf
    clt
    breq1
    mtbiri
    @0
    @2
    @1
    @0
    cA
    cpnf
    cle
    wbr
    #
    @2
    @1
    wo
    #
    cA
    pnfge
    @0
    @4
    @5
    @6
    wb
    pnfxr
    cA
    cpnf
    xrleloe
    mpan2
    mpbid
    ord
    impbid2
end
