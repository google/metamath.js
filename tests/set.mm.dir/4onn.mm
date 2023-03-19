include "c4o.mm"
include "c3o.mm"
include "csuc.mm"
include "com.mm"
include "df-4o.mm"
include "wcel.mm"
include "3onn.mm"
include "peano2.mm"
include "ax-mp.mm"
include "eqeltri.mm"

theorem 4onn



  assert |- 4o e. _om

  proof
    c4o
    c3o
    csuc
    #
    com
    df-4o
    c3o
    com
    wcel
    @0
    com
    wcel
    3onn
    c3o
    peano2
    ax-mp
    eqeltri
end
