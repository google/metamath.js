include "chom.mm"
include "c1.mm"
include "c4.mm"
include "cdc.mm"
include "df-hom.mm"
include "1nn0.mm"
include "4nn.mm"
include "decnncl.mm"
include "ndxarg.mm"

theorem homndx



  assert |- ( Hom ` ndx ) = ; 1 4

  proof
    chom
    c1
    c4
    cdc
    df-hom
    c1
    c4
    1nn0
    4nn
    decnncl
    ndxarg
end
