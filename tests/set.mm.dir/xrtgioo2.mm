include "cle.mm"
include "cordt.mm"
include "cfv.mm"
include "cr.mm"
include "crest.mm"
include "co.mm"
include "eqid.mm"
include "xrtgioo.mm"

theorem xrtgioo2



  assert |- ( topGen ` ran (,) ) = ( ( ordTop ` <_ ) |`t RR )

  proof
    cle
    cordt
    cfv
    cr
    crest
    co
    #
    @0
    eqid
    xrtgioo
end
