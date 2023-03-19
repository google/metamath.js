include "cstv.mm"
include "c4.mm"
include "df-starv.mm"
include "4nn.mm"
include "ndxarg.mm"

theorem starvndx



  assert |- ( *r ` ndx ) = 4

  proof
    cstv
    c4
    df-starv
    4nn
    ndxarg
end
