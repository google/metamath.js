include "ccnfld.mm"
include "c1.mm"
include "c3.mm"
include "cdc.mm"
include "cop.mm"
include "cstr.mm"
include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "cnfldstr.mm"
include "structex.mm"
include "ax-mp.mm"

theorem cnfldex



  assert |- CCfld e. _V

  proof
    ccnfld
    c1
    c1
    c3
    cdc
    cop
    #
    cstr
    wbr
    ccnfld
    cvv
    wcel
    cnfldstr
    ccnfld
    @0
    structex
    ax-mp
end
