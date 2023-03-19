include "chom.mm"
include "c1.mm"
include "c4.mm"
include "cdc.mm"
include "df-hom.mm"
include "1nn0.mm"
include "4nn.mm"
include "decnncl.mm"
include "ndxid.mm"

theorem homid



  assert |- Hom = Slot ( Hom ` ndx )

  proof
    chom
    c1
    c4
    cdc
    df-hom
    c1
    c4
    1nn0
    4nn
    decnncl
    ndxid
end
