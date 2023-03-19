include "cnx.mm"
include "cedgf.mm"
include "cfv.mm"
include "c1.mm"
include "c8.mm"
include "cdc.mm"
include "cn.mm"
include "df-edgf.mm"
include "1nn0.mm"
include "8nn.mm"
include "decnncl.mm"
include "ndxarg.mm"
include "eqeltri.mm"

theorem edgfndxnn



  assert |- ( .ef ` ndx ) e. NN

  proof
    cnx
    cedgf
    cfv
    c1
    c8
    cdc
    #
    cn
    cedgf
    @0
    df-edgf
    c1
    c8
    1nn0
    8nn
    decnncl
    #
    ndxarg
    @1
    eqeltri
end
