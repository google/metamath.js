include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "csigagen.mm"
include "cuni.mm"
include "cbrsiga.mm"
include "cr.mm"
include "ctop.mm"
include "wcel.mm"
include "wceq.mm"
include "retop.mm"
include "unisg.mm"
include "ax-mp.mm"
include "df-brsiga.mm"
include "unieqi.mm"
include "uniretop.mm"
include "3eqtr4i.mm"

theorem unibrsiga



  assert |- U. BrSiga = RR

  proof
    cioo
    crn
    ctg
    cfv
    #
    csigagen
    cfv
    #
    cuni
    #
    @0
    cuni
    #
    cbrsiga
    cuni
    cr
    @0
    ctop
    wcel
    @2
    @3
    wceq
    retop
    @0
    ctop
    unisg
    ax-mp
    cbrsiga
    @1
    df-brsiga
    unieqi
    uniretop
    3eqtr4i
end
