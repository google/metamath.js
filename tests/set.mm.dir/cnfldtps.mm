include "ccnfld.mm"
include "cmt.mm"
include "wcel.mm"
include "ctps.mm"
include "cnfldms.mm"
include "mstps.mm"
include "ax-mp.mm"

theorem cnfldtps



  assert |- CCfld e. TopSp

  proof
    ccnfld
    cmt
    wcel
    ccnfld
    ctps
    wcel
    cnfldms
    ccnfld
    mstps
    ax-mp
end
