include "c1.mm"
include "c3.mm"
include "cpr.mm"
include "c8.mm"
include "cin.mm"
include "csn.mm"
include "cun.mm"
include "df-pr.mm"
include "ineq2i.mm"
include "indi.mm"
include "c0.mm"
include "wss.mm"
include "wceq.mm"
include "snsspr1.mm"
include "sseqin2.mm"
include "mpbi.mm"
include "wcel.mm"
include "wn.mm"
include "1re.mm"
include "1lt8.mm"
include "gtneii.mm"
include "3re.mm"
include "3lt8.mm"
include "nelpri.mm"
include "disjsn.mm"
include "mpbir.mm"
include "uneq12i.mm"
include "un0.mm"
include "eqtri.mm"

theorem ex-in



  assert |- ( { 1 , 3 } i^i { 1 , 8 } ) = { 1 }

  proof
    c1
    c3
    cpr
    #
    c1
    c8
    cpr
    #
    cin
    @0
    c1
    csn
    #
    c8
    csn
    #
    cun
    #
    cin
    #
    @2
    @1
    @4
    @0
    c1
    c8
    df-pr
    ineq2i
    @5
    @0
    @2
    cin
    #
    @0
    @3
    cin
    #
    cun
    #
    @2
    @0
    @2
    @3
    indi
    @8
    @2
    c0
    cun
    @2
    @6
    @2
    @7
    c0
    @2
    @0
    wss
    @6
    @2
    wceq
    c1
    c3
    snsspr1
    @2
    @0
    sseqin2
    mpbi
    @7
    c0
    wceq
    c8
    @0
    wcel
    wn
    c8
    c1
    c3
    c1
    c8
    1re
    1lt8
    gtneii
    c3
    c8
    3re
    3lt8
    gtneii
    nelpri
    @0
    c8
    disjsn
    mpbir
    uneq12i
    @2
    un0
    eqtri
    eqtri
    eqtri
end
