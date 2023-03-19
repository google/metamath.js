include "c2o.mm"
include "c1o.mm"
include "csuc.mm"
include "csn.mm"
include "cun.mm"
include "c0.mm"
include "cpr.mm"
include "df-2o.mm"
include "df-suc.mm"
include "df1o2.mm"
include "uneq1i.mm"
include "df-pr.mm"
include "eqtr4i.mm"
include "3eqtri.mm"

theorem df2o3



  assert |- 2o = { (/) , 1o }

  proof
    c2o
    c1o
    csuc
    c1o
    c1o
    csn
    #
    cun
    #
    c0
    c1o
    cpr
    #
    df-2o
    c1o
    df-suc
    @1
    c0
    csn
    #
    @0
    cun
    @2
    c1o
    @3
    @0
    df1o2
    uneq1i
    c0
    c1o
    df-pr
    eqtr4i
    3eqtri
end
