include "citv.mm"
include "c1.mm"
include "c6.mm"
include "cdc.mm"
include "df-itv.mm"
include "1nn0.mm"
include "6nn.mm"
include "decnncl.mm"
include "ndxid.mm"

theorem itvid



  assert |- Itv = Slot ( Itv ` ndx )

  proof
    citv
    c1
    c6
    cdc
    df-itv
    c1
    c6
    1nn0
    6nn
    decnncl
    ndxid
end
