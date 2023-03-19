include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "c1.mm"
include "cn.mm"
include "df-base.mm"
include "1nn.mm"
include "ndxarg.mm"
include "eqeltri.mm"

theorem basendxnn



  assert |- ( Base ` ndx ) e. NN

  proof
    cnx
    cbs
    cfv
    c1
    cn
    cbs
    c1
    df-base
    1nn
    ndxarg
    1nn
    eqeltri
end
