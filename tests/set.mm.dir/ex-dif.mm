include "c1.mm"
include "c3.mm"
include "cpr.mm"
include "c8.mm"
include "cdif.mm"
include "csn.mm"
include "cun.mm"
include "df-pr.mm"
include "difeq1i.mm"
include "difundir.mm"
include "c0.mm"
include "wss.mm"
include "wceq.mm"
include "snsspr1.mm"
include "ssdif0.mm"
include "mpbi.mm"
include "cin.mm"
include "incom.mm"
include "wcel.mm"
include "wn.mm"
include "1re.mm"
include "1lt3.mm"
include "gtneii.mm"
include "3re.mm"
include "3lt8.mm"
include "ltneii.mm"
include "nelpri.mm"
include "disjsn.mm"
include "mpbir.mm"
include "eqtri.mm"
include "disj3.mm"
include "eqcomi.mm"
include "uneq12i.mm"
include "uncom.mm"
include "un0.mm"
include "3eqtri.mm"

theorem ex-dif



  assert |- ( { 1 , 3 } \ { 1 , 8 } ) = { 3 }

  proof
    c1
    c3
    cpr
    #
    c1
    c8
    cpr
    #
    cdif
    c1
    csn
    #
    c3
    csn
    #
    cun
    #
    @1
    cdif
    @2
    @1
    cdif
    #
    @3
    @1
    cdif
    #
    cun
    #
    @3
    @0
    @4
    @1
    c1
    c3
    df-pr
    difeq1i
    @2
    @3
    @1
    difundir
    @7
    c0
    @3
    cun
    @3
    c0
    cun
    @3
    @5
    c0
    @6
    @3
    @2
    @1
    wss
    @5
    c0
    wceq
    c1
    c8
    snsspr1
    @2
    @1
    ssdif0
    mpbi
    @3
    @6
    @3
    @1
    cin
    #
    c0
    wceq
    @3
    @6
    wceq
    @8
    @1
    @3
    cin
    #
    c0
    @3
    @1
    incom
    @9
    c0
    wceq
    c3
    @1
    wcel
    wn
    c3
    c1
    c8
    c1
    c3
    1re
    1lt3
    gtneii
    c3
    c8
    3re
    3lt8
    ltneii
    nelpri
    @1
    c3
    disjsn
    mpbir
    eqtri
    @3
    @1
    disj3
    mpbi
    eqcomi
    uneq12i
    c0
    @3
    uncom
    @3
    un0
    3eqtri
    3eqtri
end
