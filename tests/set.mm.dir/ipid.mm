include "cip.mm"
include "c8.mm"
include "df-ip.mm"
include "8nn.mm"
include "ndxid.mm"

theorem ipid



  assert |- .i = Slot ( .i ` ndx )

  proof
    cip
    c8
    df-ip
    8nn
    ndxid
end
