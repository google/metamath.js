include "cbs.mm"
include "c1.mm"
include "df-base.mm"
include "1nn.mm"
include "ndxarg.mm"

theorem basendx



  assert |- ( Base ` ndx ) = 1

  proof
    cbs
    c1
    df-base
    1nn
    ndxarg
end
