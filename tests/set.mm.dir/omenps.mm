include "com.mm"
include "cvv.mm"
include "wcel.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "cen.mm"
include "wbr.mm"
include "omex.mm"
include "limom.mm"
include "limenpsi.mm"
include "ax-mp.mm"

theorem omenps



  assert |- _om ~~ ( _om \ { (/) } )

  proof
    com
    cvv
    wcel
    com
    com
    c0
    csn
    cdif
    cen
    wbr
    omex
    com
    cvv
    limom
    limenpsi
    ax-mp
end
