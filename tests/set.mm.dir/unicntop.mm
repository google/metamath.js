include "cc.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "eqid.mm"
include "cnfldtopon.mm"
include "toponunii.mm"

theorem unicntop



  assert |- CC = U. ( TopOpen ` CCfld )

  proof
    cc
    ccnfld
    ctopn
    cfv
    #
    @0
    @0
    eqid
    cnfldtopon
    toponunii
end
