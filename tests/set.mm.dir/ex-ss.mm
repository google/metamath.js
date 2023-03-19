include "c1.mm"
include "c2.mm"
include "cpr.mm"
include "c3.mm"
include "csn.mm"
include "cun.mm"
include "ctp.mm"
include "ssun1.mm"
include "df-tp.mm"
include "sseqtr4i.mm"

theorem ex-ss



  assert |- { 1 , 2 } C_ { 1 , 2 , 3 }

  proof
    c1
    c2
    cpr
    #
    @0
    c3
    csn
    #
    cun
    c1
    c2
    c3
    ctp
    @0
    @1
    ssun1
    c1
    c2
    c3
    df-tp
    sseqtr4i
end
