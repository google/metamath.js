include "cpnf.mm"
include "cxnn0.mm"
include "wcel.mm"
include "cn0.mm"
include "wceq.mm"
include "wo.mm"
include "eqid.mm"
include "olci.mm"
include "elxnn0.mm"
include "mpbir.mm"

theorem pnf0xnn0



  assert |- +oo e. NN0*

  proof
    cpnf
    cxnn0
    wcel
    cpnf
    cn0
    wcel
    #
    cpnf
    cpnf
    wceq
    #
    wo
    @1
    @0
    cpnf
    eqid
    olci
    cpnf
    elxnn0
    mpbir
end
