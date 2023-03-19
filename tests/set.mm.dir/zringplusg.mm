include "cz.mm"
include "cvv.mm"
include "wcel.mm"
include "caddc.mm"
include "zring.mm"
include "cplusg.mm"
include "cfv.mm"
include "wceq.mm"
include "zex.mm"
include "ccnfld.mm"
include "df-zring.mm"
include "cnfldadd.mm"
include "ressplusg.mm"
include "ax-mp.mm"

theorem zringplusg



  assert |- + = ( +g ` ZZring )

  proof
    cz
    cvv
    wcel
    caddc
    zring
    cplusg
    cfv
    wceq
    zex
    cz
    caddc
    ccnfld
    zring
    cvv
    df-zring
    cnfldadd
    ressplusg
    ax-mp
end
