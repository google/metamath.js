include "ccnfld.mm"
include "cnrg.mm"
include "wcel.mm"
include "cngp.mm"
include "cabs.mm"
include "cabv.mm"
include "cfv.mm"
include "cnngp.mm"
include "absabv.mm"
include "cnfldnm.mm"
include "eqid.mm"
include "isnrg.mm"
include "mpbir2an.mm"

theorem cnnrg



  assert |- CCfld e. NrmRing

  proof
    ccnfld
    cnrg
    wcel
    ccnfld
    cngp
    wcel
    cabs
    ccnfld
    cabv
    cfv
    #
    wcel
    cnngp
    absabv
    @0
    ccnfld
    cabs
    cnfldnm
    @0
    eqid
    isnrg
    mpbir2an
end
