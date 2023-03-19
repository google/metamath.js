include "csca.mm"
include "c5.mm"
include "df-sca.mm"
include "5nn.mm"
include "ndxid.mm"

theorem scaid



  assert |- Scalar = Slot ( Scalar ` ndx )

  proof
    csca
    c5
    df-sca
    5nn
    ndxid
end
