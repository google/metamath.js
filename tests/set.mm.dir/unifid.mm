include "cunif.mm"
include "c1.mm"
include "c3.mm"
include "cdc.mm"
include "df-unif.mm"
include "1nn0.mm"
include "3nn.mm"
include "decnncl.mm"
include "ndxid.mm"

theorem unifid



  assert |- UnifSet = Slot ( UnifSet ` ndx )

  proof
    cunif
    c1
    c3
    cdc
    df-unif
    c1
    c3
    1nn0
    3nn
    decnncl
    ndxid
end
