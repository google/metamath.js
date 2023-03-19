include "cplusg.mm"
include "c2.mm"
include "df-plusg.mm"
include "2nn.mm"
include "ndxarg.mm"

theorem plusgndx



  assert |- ( +g ` ndx ) = 2

  proof
    cplusg
    c2
    df-plusg
    2nn
    ndxarg
end
