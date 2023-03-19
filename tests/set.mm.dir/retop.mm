include "cioo.mm"
include "crn.mm"
include "ctb.mm"
include "wcel.mm"
include "ctg.mm"
include "cfv.mm"
include "ctop.mm"
include "retopbas.mm"
include "tgcl.mm"
include "ax-mp.mm"

theorem retop



  assert |- ( topGen ` ran (,) ) e. Top

  proof
    cioo
    crn
    #
    ctb
    wcel
    @0
    ctg
    cfv
    ctop
    wcel
    retopbas
    @0
    tgcl
    ax-mp
end
