include "cmulr.mm"
include "c3.mm"
include "df-mulr.mm"
include "3nn.mm"
include "ndxid.mm"

theorem mulrid



  assert |- .r = Slot ( .r ` ndx )

  proof
    cmulr
    c3
    df-mulr
    3nn
    ndxid
end
