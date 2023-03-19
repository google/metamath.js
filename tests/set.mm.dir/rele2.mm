include "cr.mm"
include "cvv.mm"
include "wcel.mm"
include "cle.mm"
include "crefld.mm"
include "cple.mm"
include "cfv.mm"
include "wceq.mm"
include "reex.mm"
include "ccnfld.mm"
include "df-refld.mm"
include "cnfldle.mm"
include "ressle.mm"
include "ax-mp.mm"

theorem rele2



  assert |- <_ = ( le ` RRfld )

  proof
    cr
    cvv
    wcel
    cle
    crefld
    cple
    cfv
    wceq
    reex
    cr
    ccnfld
    cle
    cvv
    crefld
    df-refld
    cnfldle
    ressle
    ax-mp
end
