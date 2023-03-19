include "c3o.mm"
include "c2o.mm"
include "csuc.mm"
include "c0.mm"
include "csn.mm"
include "cpr.mm"
include "ctp.mm"
include "df-3o.mm"
include "cun.mm"
include "df2o2.mm"
include "sneqi.mm"
include "uneq12i.mm"
include "df-suc.mm"
include "df-tp.mm"
include "3eqtr4i.mm"
include "eqtri.mm"

theorem df3o3



  assert |- 3o = { (/) , { (/) } , { (/) , { (/) } } }

  proof
    c3o
    c2o
    csuc
    #
    c0
    c0
    csn
    #
    c0
    @1
    cpr
    #
    ctp
    #
    df-3o
    c2o
    c2o
    csn
    #
    cun
    @2
    @2
    csn
    #
    cun
    @0
    @3
    c2o
    @2
    @4
    @5
    df2o2
    c2o
    @2
    df2o2
    sneqi
    uneq12i
    c2o
    df-suc
    c0
    @1
    @2
    df-tp
    3eqtr4i
    eqtri
end
