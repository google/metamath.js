include "cpnf.mm"
include "cr.mm"
include "cmnf.mm"
include "cpr.mm"
include "cun.mm"
include "cxr.mm"
include "ssun2.mm"
include "cc.mm"
include "cuni.mm"
include "cpw.mm"
include "cvv.mm"
include "df-pnf.mm"
include "cnex.mm"
include "uniex.mm"
include "pwex.mm"
include "eqeltri.mm"
include "prid1.mm"
include "sselii.mm"
include "df-xr.mm"
include "eleqtrri.mm"

theorem pnfxr



  assert |- +oo e. RR*

  proof
    cpnf
    cr
    cpnf
    cmnf
    cpr
    #
    cun
    #
    cxr
    @0
    @1
    cpnf
    @0
    cr
    ssun2
    cpnf
    cmnf
    cpnf
    cc
    cuni
    #
    cpw
    cvv
    df-pnf
    @2
    cc
    cnex
    uniex
    pwex
    eqeltri
    prid1
    sselii
    df-xr
    eleqtrri
end
