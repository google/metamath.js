include "cmnf.mm"
include "cr.mm"
include "cpnf.mm"
include "cpr.mm"
include "cun.mm"
include "cxr.mm"
include "wcel.mm"
include "cpw.mm"
include "cvv.mm"
include "df-mnf.mm"
include "pnfex.mm"
include "pwex.mm"
include "eqeltri.mm"
include "prid2.mm"
include "elun2.mm"
include "ax-mp.mm"
include "df-xr.mm"
include "eleqtrri.mm"

theorem mnfxr



  assert |- -oo e. RR*

  proof
    cmnf
    cr
    cpnf
    cmnf
    cpr
    #
    cun
    #
    cxr
    cmnf
    @0
    wcel
    cmnf
    @1
    wcel
    cpnf
    cmnf
    cmnf
    cpnf
    cpw
    cvv
    df-mnf
    cpnf
    pnfex
    pwex
    eqeltri
    prid2
    cmnf
    @0
    cr
    elun2
    ax-mp
    df-xr
    eleqtrri
end
