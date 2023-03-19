include "c1o.mm"
include "c0.mm"
include "csuc.mm"
include "com.mm"
include "df-1o.mm"
include "wcel.mm"
include "peano1.mm"
include "peano2.mm"
include "ax-mp.mm"
include "eqeltri.mm"

theorem 1onn



  assert |- 1o e. _om

  proof
    c1o
    c0
    csuc
    #
    com
    df-1o
    c0
    com
    wcel
    @0
    com
    wcel
    peano1
    c0
    peano2
    ax-mp
    eqeltri
end
