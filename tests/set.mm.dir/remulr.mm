include "cr.mm"
include "cvv.mm"
include "wcel.mm"
include "cmul.mm"
include "crefld.mm"
include "cmulr.mm"
include "cfv.mm"
include "wceq.mm"
include "reex.mm"
include "ccnfld.mm"
include "df-refld.mm"
include "cnfldmul.mm"
include "ressmulr.mm"
include "ax-mp.mm"

theorem remulr



  assert |- x. = ( .r ` RRfld )

  proof
    cr
    cvv
    wcel
    cmul
    crefld
    cmulr
    cfv
    wceq
    reex
    cr
    ccnfld
    crefld
    cmul
    cvv
    df-refld
    cnfldmul
    ressmulr
    ax-mp
end
