include "cr.mm"
include "cioo.mm"
include "crn.mm"
include "cuni.mm"
include "ctg.mm"
include "cfv.mm"
include "unirnioo.mm"
include "ctb.mm"
include "wcel.mm"
include "wceq.mm"
include "retopbas.mm"
include "unitg.mm"
include "ax-mp.mm"
include "eqtr4i.mm"

theorem uniretop



  assert |- RR = U. ( topGen ` ran (,) )

  proof
    cr
    cioo
    crn
    #
    cuni
    #
    @0
    ctg
    cfv
    cuni
    #
    unirnioo
    @0
    ctb
    wcel
    @2
    @1
    wceq
    retopbas
    @0
    ctb
    unitg
    ax-mp
    eqtr4i
end
