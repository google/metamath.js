include "cxr.mm"
include "cr.mm"
include "cpnf.mm"
include "cmnf.mm"
include "cpr.mm"
include "cun.mm"
include "cvv.mm"
include "df-xr.mm"
include "reex.mm"
include "prex.mm"
include "unex.mm"
include "eqeltri.mm"

theorem xrex



  assert |- RR* e. _V

  proof
    cxr
    cr
    cpnf
    cmnf
    cpr
    #
    cun
    cvv
    df-xr
    cr
    @0
    reex
    cpnf
    cmnf
    prex
    unex
    eqeltri
end
