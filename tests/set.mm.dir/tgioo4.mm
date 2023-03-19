include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "eqid.mm"
include "tgioo2.mm"

theorem tgioo4



  assert |- ( topGen ` ran (,) ) = ( ( TopOpen ` CCfld ) |`t RR )

  proof
    ccnfld
    ctopn
    cfv
    #
    @0
    eqid
    tgioo2
end
