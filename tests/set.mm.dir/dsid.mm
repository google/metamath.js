include "cds.mm"
include "c1.mm"
include "c2.mm"
include "cdc.mm"
include "df-ds.mm"
include "1nn0.mm"
include "2nn.mm"
include "decnncl.mm"
include "ndxid.mm"

theorem dsid



  assert |- dist = Slot ( dist ` ndx )

  proof
    cds
    c1
    c2
    cdc
    df-ds
    c1
    c2
    1nn0
    2nn
    decnncl
    ndxid
end
