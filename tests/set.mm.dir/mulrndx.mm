include "cmulr.mm"
include "c3.mm"
include "df-mulr.mm"
include "3nn.mm"
include "ndxarg.mm"

theorem mulrndx



  assert |- ( .r ` ndx ) = 3

  proof
    cmulr
    c3
    df-mulr
    3nn
    ndxarg
end
