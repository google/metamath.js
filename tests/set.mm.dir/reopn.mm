include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "ctop.mm"
include "wcel.mm"
include "cr.mm"
include "retop.mm"
include "uniretop.mm"
include "topopn.mm"
include "ax-mp.mm"

theorem reopn



  assert |- RR e. ( topGen ` ran (,) )

  proof
    cioo
    crn
    ctg
    cfv
    #
    ctop
    wcel
    cr
    @0
    wcel
    retop
    @0
    cr
    uniretop
    topopn
    ax-mp
end
