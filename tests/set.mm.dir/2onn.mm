include "c2o.mm"
include "c1o.mm"
include "csuc.mm"
include "com.mm"
include "df-2o.mm"
include "wcel.mm"
include "1onn.mm"
include "peano2.mm"
include "ax-mp.mm"
include "eqeltri.mm"

theorem 2onn



  assert |- 2o e. _om

  proof
    c2o
    c1o
    csuc
    #
    com
    df-2o
    c1o
    com
    wcel
    @0
    com
    wcel
    1onn
    c1o
    peano2
    ax-mp
    eqeltri
end
