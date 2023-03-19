include "ccnfld.mm"
include "cmt.mm"
include "wcel.mm"
include "cxme.mm"
include "cnfldms.mm"
include "msxms.mm"
include "ax-mp.mm"

theorem cnfldxms



  assert |- CCfld e. *MetSp

  proof
    ccnfld
    cmt
    wcel
    ccnfld
    cxme
    wcel
    cnfldms
    ccnfld
    msxms
    ax-mp
end
