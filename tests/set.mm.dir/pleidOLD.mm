include "cple.mm"
include "c10.mm"
include "dfpleOLD.mm"
include "10nnOLD.mm"
include "ndxid.mm"

theorem pleidOLD



  assert |- le = Slot ( le ` ndx )

  proof
    cple
    c10
    dfpleOLD
    10nnOLD
    ndxid
end
