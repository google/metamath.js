include "cco.mm"
include "c1.mm"
include "c5.mm"
include "cdc.mm"
include "df-cco.mm"
include "1nn0.mm"
include "5nn.mm"
include "decnncl.mm"
include "ndxid.mm"

theorem ccoid



  assert |- comp = Slot ( comp ` ndx )

  proof
    cco
    c1
    c5
    cdc
    df-cco
    c1
    c5
    1nn0
    5nn
    decnncl
    ndxid
end
