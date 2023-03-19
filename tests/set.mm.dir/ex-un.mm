include "c1.mm"
include "c3.mm"
include "cpr.mm"
include "csn.mm"
include "c8.mm"
include "cun.mm"
include "ctp.mm"
include "unass.mm"
include "wss.mm"
include "wceq.mm"
include "snsspr1.mm"
include "ssequn2.mm"
include "mpbi.mm"
include "uneq1i.mm"
include "eqtr3i.mm"
include "df-pr.mm"
include "uneq2i.mm"
include "df-tp.mm"
include "3eqtr4i.mm"

theorem ex-un



  assert |- ( { 1 , 3 } u. { 1 , 8 } ) = { 1 , 3 , 8 }

  proof
    c1
    c3
    cpr
    #
    c1
    csn
    #
    c8
    csn
    #
    cun
    #
    cun
    #
    @0
    @2
    cun
    #
    @0
    c1
    c8
    cpr
    #
    cun
    c1
    c3
    c8
    ctp
    @0
    @1
    cun
    #
    @2
    cun
    @4
    @5
    @0
    @1
    @2
    unass
    @7
    @0
    @2
    @1
    @0
    wss
    @7
    @0
    wceq
    c1
    c3
    snsspr1
    @1
    @0
    ssequn2
    mpbi
    uneq1i
    eqtr3i
    @6
    @3
    @0
    c1
    c8
    df-pr
    uneq2i
    c1
    c3
    c8
    df-tp
    3eqtr4i
end
