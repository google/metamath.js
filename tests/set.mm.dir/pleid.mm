include "cple.mm"
include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "df-ple.mm"
include "10nn.mm"
include "ndxid.mm"

theorem pleid



  assert |- le = Slot ( le ` ndx )

  proof
    cple
    c1
    cc0
    cdc
    df-ple
    10nn
    ndxid
end
