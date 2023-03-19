include "cz.mm"
include "cvv.mm"
include "wcel.mm"
include "cmul.mm"
include "zring.mm"
include "cmulr.mm"
include "cfv.mm"
include "wceq.mm"
include "zex.mm"
include "ccnfld.mm"
include "df-zring.mm"
include "cnfldmul.mm"
include "ressmulr.mm"
include "ax-mp.mm"

theorem zringmulr



  assert |- x. = ( .r ` ZZring )

  proof
    cz
    cvv
    wcel
    cmul
    zring
    cmulr
    cfv
    wceq
    zex
    cz
    ccnfld
    zring
    cmul
    cvv
    df-zring
    cnfldmul
    ressmulr
    ax-mp
end
