include "c1o.mm"
include "c0.mm"
include "csuc.mm"
include "csn.mm"
include "df-1o.mm"
include "suc0.mm"
include "eqtri.mm"

theorem df1o2



  assert |- 1o = { (/) }

  proof
    c1o
    c0
    csuc
    c0
    csn
    df-1o
    suc0
    eqtri
end
