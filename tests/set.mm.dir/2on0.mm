include "c2o.mm"
include "c1o.mm"
include "csuc.mm"
include "c0.mm"
include "df-2o.mm"
include "nsuceq0.mm"
include "eqnetri.mm"

theorem 2on0



  assert |- 2o =/= (/)

  proof
    c2o
    c1o
    csuc
    c0
    df-2o
    c1o
    nsuceq0
    eqnetri
end
