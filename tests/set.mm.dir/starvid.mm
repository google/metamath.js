include "cstv.mm"
include "c4.mm"
include "df-starv.mm"
include "4nn.mm"
include "ndxid.mm"

theorem starvid



  assert |- *r = Slot ( *r ` ndx )

  proof
    cstv
    c4
    df-starv
    4nn
    ndxid
end
