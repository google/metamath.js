include "cplusg.mm"
include "c2.mm"
include "df-plusg.mm"
include "2nn.mm"
include "ndxid.mm"

theorem plusgid



  assert |- +g = Slot ( +g ` ndx )

  proof
    cplusg
    c2
    df-plusg
    2nn
    ndxid
end
