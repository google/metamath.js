include "c2o.mm"
include "c1o.mm"
include "csuc.mm"
include "con0.mm"
include "df-2o.mm"
include "1on.mm"
include "onsuci.mm"
include "eqeltri.mm"

theorem 2on



  assert |- 2o e. On

  proof
    c2o
    c1o
    csuc
    con0
    df-2o
    c1o
    1on
    onsuci
    eqeltri
end
