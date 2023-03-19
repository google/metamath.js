include "cr.mm"
include "cvv.mm"
include "wcel.mm"
include "ccj.mm"
include "crefld.mm"
include "cstv.mm"
include "cfv.mm"
include "wceq.mm"
include "reex.mm"
include "ccnfld.mm"
include "df-refld.mm"
include "cnfldcj.mm"
include "ressstarv.mm"
include "ax-mp.mm"

theorem refldcj



  assert |- * = ( *r ` RRfld )

  proof
    cr
    cvv
    wcel
    ccj
    crefld
    cstv
    cfv
    wceq
    reex
    cr
    ccnfld
    crefld
    ccj
    cvv
    df-refld
    cnfldcj
    ressstarv
    ax-mp
end
