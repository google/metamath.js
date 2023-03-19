include "c3o.mm"
include "c2o.mm"
include "csuc.mm"
include "com.mm"
include "df-3o.mm"
include "wcel.mm"
include "2onn.mm"
include "peano2.mm"
include "ax-mp.mm"
include "eqeltri.mm"

theorem 3onn



  assert |- 3o e. _om

  proof
    c3o
    c2o
    csuc
    #
    com
    df-3o
    c2o
    com
    wcel
    @0
    com
    wcel
    2onn
    c2o
    peano2
    ax-mp
    eqeltri
end
