include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "cmnf.mm"
include "cpnf.mm"
include "co.mm"
include "crest.mm"
include "csconn.mm"
include "ctop.mm"
include "wcel.mm"
include "wceq.mm"
include "retop.mm"
include "cr.mm"
include "cuni.mm"
include "ioomax.mm"
include "uniretop.mm"
include "eqtri.mm"
include "restid.mm"
include "ax-mp.mm"
include "ioosconn.mm"
include "eqeltrri.mm"

theorem retopsconn



  assert |- ( topGen ` ran (,) ) e. SConn

  proof
    cioo
    crn
    ctg
    cfv
    #
    cmnf
    cpnf
    cioo
    co
    #
    crest
    co
    #
    @0
    csconn
    @0
    ctop
    wcel
    @2
    @0
    wceq
    retop
    @0
    ctop
    @1
    @1
    cr
    @0
    cuni
    ioomax
    uniretop
    eqtri
    restid
    ax-mp
    cmnf
    cpnf
    ioosconn
    eqeltrri
end
