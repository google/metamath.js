include "cedgf.mm"
include "c1.mm"
include "c8.mm"
include "cdc.mm"
include "df-edgf.mm"
include "1nn0.mm"
include "8nn.mm"
include "decnncl.mm"
include "ndxid.mm"

theorem edgfid



  assert |- .ef = Slot ( .ef ` ndx )

  proof
    cedgf
    c1
    c8
    cdc
    df-edgf
    c1
    c8
    1nn0
    8nn
    decnncl
    ndxid
end
