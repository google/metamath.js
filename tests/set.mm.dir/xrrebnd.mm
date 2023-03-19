include "cxr.mm"
include "wcel.mm"
include "cr.mm"
include "cmnf.mm"
include "clt.mm"
include "wbr.mm"
include "cpnf.mm"
include "wa.mm"
include "mnflt.mm"
include "ltpnf.mm"
include "jca.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "nltpnft.mm"
include "ngtmnft.mm"
include "orbi12d.mm"
include "ianor.mm"
include "orcom.mm"
include "bitr2i.mm"
include "syl6bb.mm"
include "con2bid.mm"
include "w3o.mm"
include "elxr.mm"
include "3orass.mm"
include "bitri.mm"
include "sylbb.mm"
include "ord.mm"
include "sylbid.mm"
include "impbid2.mm"

theorem xrrebnd
  let cA: class A


  assert |- ( A e. RR* -> ( A e. RR <-> ( -oo < A /\ A < +oo ) ) )

  proof
    cA
    cxr
    wcel
    #
    cA
    cr
    wcel
    #
    cmnf
    cA
    clt
    wbr
    #
    cA
    cpnf
    clt
    wbr
    #
    wa
    #
    @1
    @2
    @3
    cA
    mnflt
    cA
    ltpnf
    jca
    @0
    @4
    cA
    cpnf
    wceq
    #
    cA
    cmnf
    wceq
    #
    wo
    #
    wn
    @1
    @0
    @7
    @4
    @0
    @7
    @3
    wn
    #
    @2
    wn
    #
    wo
    #
    @4
    wn
    #
    @0
    @5
    @8
    @6
    @9
    cA
    nltpnft
    cA
    ngtmnft
    orbi12d
    @11
    @9
    @8
    wo
    @10
    @2
    @3
    ianor
    @9
    @8
    orcom
    bitr2i
    syl6bb
    con2bid
    @0
    @7
    @1
    @0
    @1
    @5
    @6
    w3o
    #
    @7
    @1
    wo
    #
    cA
    elxr
    @12
    @1
    @7
    wo
    @13
    @1
    @5
    @6
    3orass
    @1
    @7
    orcom
    bitri
    sylbb
    ord
    sylbid
    impbid2
end
