include "cr.mm"
include "cvv.mm"
include "wcel.mm"
include "caddc.mm"
include "crefld.mm"
include "cplusg.mm"
include "cfv.mm"
include "wceq.mm"
include "reex.mm"
include "ccnfld.mm"
include "df-refld.mm"
include "cnfldadd.mm"
include "ressplusg.mm"
include "ax-mp.mm"

theorem replusg



  assert |- + = ( +g ` RRfld )

  proof
    cr
    cvv
    wcel
    caddc
    crefld
    cplusg
    cfv
    wceq
    reex
    cr
    caddc
    ccnfld
    crefld
    cvv
    df-refld
    cnfldadd
    ressplusg
    ax-mp
end
