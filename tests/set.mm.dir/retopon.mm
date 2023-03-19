include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "ctop.mm"
include "wcel.mm"
include "cr.mm"
include "ctopon.mm"
include "retop.mm"
include "uniretop.mm"
include "toptopon.mm"
include "mpbi.mm"

theorem retopon



  assert |- ( topGen ` ran (,) ) e. ( TopOn ` RR )

  proof
    cioo
    crn
    ctg
    cfv
    #
    ctop
    wcel
    @0
    cr
    ctopon
    cfv
    wcel
    retop
    @0
    cr
    uniretop
    toptopon
    mpbi
end
