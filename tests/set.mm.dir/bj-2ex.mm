include "c2o.mm"
include "c1o.mm"
include "csuc.mm"
include "cvv.mm"
include "df-2o.mm"
include "bj-1ex.mm"
include "sucex.mm"
include "eqeltri.mm"

theorem bj-2ex



  assert |- 2o e. _V

  proof
    c2o
    c1o
    csuc
    cvv
    df-2o
    c1o
    bj-1ex
    sucex
    eqeltri
end
