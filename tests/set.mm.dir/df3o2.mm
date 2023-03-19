include "c3o.mm"
include "c2o.mm"
include "csuc.mm"
include "c0.mm"
include "c1o.mm"
include "ctp.mm"
include "df-3o.mm"
include "csn.mm"
include "cun.mm"
include "cpr.mm"
include "df2o3.mm"
include "uneq1i.mm"
include "df-suc.mm"
include "df-tp.mm"
include "3eqtr4i.mm"
include "eqtri.mm"

theorem df3o2



  assert |- 3o = { (/) , 1o , 2o }

  proof
    c3o
    c2o
    csuc
    #
    c0
    c1o
    c2o
    ctp
    #
    df-3o
    c2o
    c2o
    csn
    #
    cun
    c0
    c1o
    cpr
    #
    @2
    cun
    @0
    @1
    c2o
    @3
    @2
    df2o3
    uneq1i
    c2o
    df-suc
    c0
    c1o
    c2o
    df-tp
    3eqtr4i
    eqtri
end
