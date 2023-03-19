include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "c1.mm"
include "cmulr.mm"
include "df-base.mm"
include "1nn.mm"
include "ndxarg.mm"
include "c3.mm"
include "1re.mm"
include "1lt3.mm"
include "ltneii.mm"
include "mulrndx.mm"
include "neeqtrri.mm"
include "eqnetri.mm"

theorem basendxnmulrndx



  assert |- ( Base ` ndx ) =/= ( .r ` ndx )

  proof
    cnx
    cbs
    cfv
    c1
    cnx
    cmulr
    cfv
    #
    cbs
    c1
    df-base
    1nn
    ndxarg
    c1
    c3
    @0
    c1
    c3
    1re
    1lt3
    ltneii
    mulrndx
    neeqtrri
    eqnetri
end
