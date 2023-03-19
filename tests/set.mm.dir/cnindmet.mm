include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cds.mm"
include "cfv.mm"
include "ccnfld.mm"
include "cabv.mm"
include "wcel.mm"
include "wceq.mm"
include "absabv.mm"
include "cnfldsub.mm"
include "tngds.mm"
include "ax-mp.mm"
include "eqcomi.mm"

theorem cnindmet
  let cT: class T
  assume cnindmet.t: |- T = ( CCfld toNrmGrp abs )


  assert |- ( dist ` T ) = ( abs o. - )

  proof
    cabs
    cmin
    ccom
    #
    cT
    cds
    cfv
    #
    cabs
    ccnfld
    cabv
    cfv
    #
    wcel
    @0
    @1
    wceq
    absabv
    cT
    ccnfld
    cmin
    cabs
    @2
    cnindmet.t
    cnfldsub
    tngds
    ax-mp
    eqcomi
end
