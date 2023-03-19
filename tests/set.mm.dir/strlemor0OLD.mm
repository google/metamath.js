include "c0.mm"
include "ccnv.mm"
include "wfun.mm"
include "cdm.mm"
include "c1.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wss.mm"
include "fun0.mm"
include "funcnvcnv.mm"
include "ax-mp.mm"
include "dm0.mm"
include "0ss.mm"
include "eqsstri.mm"
include "pm3.2i.mm"

theorem strlemor0OLD



  assert |- ( Fun `' `' (/) /\ dom (/) C_ ( 1 ... 0 ) )

  proof
    c0
    ccnv
    ccnv
    wfun
    #
    c0
    cdm
    #
    c1
    cc0
    cfz
    co
    #
    wss
    c0
    wfun
    @0
    fun0
    c0
    funcnvcnv
    ax-mp
    @1
    c0
    @2
    dm0
    @2
    0ss
    eqsstri
    pm3.2i
end
