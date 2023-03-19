include "cco.mm"
include "c1.mm"
include "c5.mm"
include "cdc.mm"
include "df-cco.mm"
include "1nn0.mm"
include "5nn.mm"
include "decnncl.mm"
include "ndxarg.mm"

theorem ccondx



  assert |- ( comp ` ndx ) = ; 1 5

  proof
    cco
    c1
    c5
    cdc
    df-cco
    c1
    c5
    1nn0
    5nn
    decnncl
    ndxarg
end
