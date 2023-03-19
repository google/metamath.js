include "cvsca.mm"
include "c6.mm"
include "df-vsca.mm"
include "6nn.mm"
include "ndxarg.mm"

theorem vscandx



  assert |- ( .s ` ndx ) = 6

  proof
    cvsca
    c6
    df-vsca
    6nn
    ndxarg
end
