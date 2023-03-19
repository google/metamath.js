include "csca.mm"
include "c5.mm"
include "df-sca.mm"
include "5nn.mm"
include "ndxarg.mm"

theorem scandx



  assert |- ( Scalar ` ndx ) = 5

  proof
    csca
    c5
    df-sca
    5nn
    ndxarg
end
