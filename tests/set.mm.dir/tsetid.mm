include "cts.mm"
include "c9.mm"
include "df-tset.mm"
include "9nn.mm"
include "ndxid.mm"

theorem tsetid



  assert |- TopSet = Slot ( TopSet ` ndx )

  proof
    cts
    c9
    df-tset
    9nn
    ndxid
end
