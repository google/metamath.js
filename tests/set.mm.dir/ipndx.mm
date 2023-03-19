include "cip.mm"
include "c8.mm"
include "df-ip.mm"
include "8nn.mm"
include "ndxarg.mm"

theorem ipndx



  assert |- ( .i ` ndx ) = 8

  proof
    cip
    c8
    df-ip
    8nn
    ndxarg
end
