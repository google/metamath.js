include "c1o.mm"
include "c0.mm"
include "csuc.mm"
include "cvv.mm"
include "df-1o.mm"
include "0ex.mm"
include "sucex.mm"
include "eqeltri.mm"

theorem bj-1ex



  assert |- 1o e. _V

  proof
    c1o
    c0
    csuc
    cvv
    df-1o
    c0
    0ex
    sucex
    eqeltri
end
