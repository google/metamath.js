include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "c1.mm"
include "cplusg.mm"
include "df-base.mm"
include "1nn.mm"
include "ndxarg.mm"
include "c2.mm"
include "1ne2.mm"
include "plusgndx.mm"
include "neeqtrri.mm"
include "eqnetri.mm"

theorem basendxnplusgndx



  assert |- ( Base ` ndx ) =/= ( +g ` ndx )

  proof
    cnx
    cbs
    cfv
    c1
    cnx
    cplusg
    cfv
    #
    cbs
    c1
    df-base
    1nn
    ndxarg
    c1
    c2
    @0
    1ne2
    plusgndx
    neeqtrri
    eqnetri
end
