include "c2o.mm"
include "c0.mm"
include "c1o.mm"
include "cpr.mm"
include "csn.mm"
include "df2o3.mm"
include "df1o2.mm"
include "preq2i.mm"
include "eqtri.mm"

theorem df2o2



  assert |- 2o = { (/) , { (/) } }

  proof
    c2o
    c0
    c1o
    cpr
    c0
    c0
    csn
    #
    cpr
    df2o3
    c1o
    @0
    c0
    df1o2
    preq2i
    eqtri
end
