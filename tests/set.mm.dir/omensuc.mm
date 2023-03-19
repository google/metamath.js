include "com.mm"
include "cvv.mm"
include "wcel.mm"
include "csuc.mm"
include "cen.mm"
include "wbr.mm"
include "omex.mm"
include "limom.mm"
include "limensuci.mm"
include "ax-mp.mm"

theorem omensuc



  assert |- _om ~~ suc _om

  proof
    com
    cvv
    wcel
    com
    com
    csuc
    cen
    wbr
    omex
    com
    cvv
    limom
    limensuci
    ax-mp
end
