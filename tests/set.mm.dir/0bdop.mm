include "ch0o.mm"
include "cbo.mm"
include "wcel.mm"
include "clo.mm"
include "cnop.mm"
include "cfv.mm"
include "cpnf.mm"
include "clt.mm"
include "wbr.mm"
include "0lnop.mm"
include "cc0.mm"
include "nmop0.mm"
include "0ltpnf.mm"
include "eqbrtri.mm"
include "elbdop.mm"
include "mpbir2an.mm"

theorem 0bdop



  assert |- 0hop e. BndLinOp

  proof
    ch0o
    cbo
    wcel
    ch0o
    clo
    wcel
    ch0o
    cnop
    cfv
    #
    cpnf
    clt
    wbr
    0lnop
    @0
    cc0
    cpnf
    clt
    nmop0
    0ltpnf
    eqbrtri
    ch0o
    elbdop
    mpbir2an
end
