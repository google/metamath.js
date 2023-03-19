include "cvsca.mm"
include "c6.mm"
include "df-vsca.mm"
include "6nn.mm"
include "ndxid.mm"

theorem vscaid



  assert |- .s = Slot ( .s ` ndx )

  proof
    cvsca
    c6
    df-vsca
    6nn
    ndxid
end
