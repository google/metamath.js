include "cbs.mm"
include "c1.mm"
include "df-base.mm"
include "1nn.mm"
include "ndxid.mm"

theorem baseid



  assert |- Base = Slot ( Base ` ndx )

  proof
    cbs
    c1
    df-base
    1nn
    ndxid
end
