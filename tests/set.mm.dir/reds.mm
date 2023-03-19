include "cr.mm"
include "cvv.mm"
include "wcel.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "crefld.mm"
include "cds.mm"
include "cfv.mm"
include "wceq.mm"
include "reex.mm"
include "ccnfld.mm"
include "df-refld.mm"
include "cnfldds.mm"
include "ressds.mm"
include "ax-mp.mm"

theorem reds



  assert |- ( abs o. - ) = ( dist ` RRfld )

  proof
    cr
    cvv
    wcel
    cabs
    cmin
    ccom
    #
    crefld
    cds
    cfv
    wceq
    reex
    cr
    @0
    ccnfld
    crefld
    cvv
    df-refld
    cnfldds
    ressds
    ax-mp
end
