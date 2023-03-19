include "ccnfld.mm"
include "ctps.mm"
include "wcel.mm"
include "cc.mm"
include "ctopon.mm"
include "cfv.mm"
include "cnfldtps.mm"
include "cnfldbas.mm"
include "istps.mm"
include "mpbi.mm"

theorem cnfldtopon
  let cJ: class J
  assume cnfldtopn.1: |- J = ( TopOpen ` CCfld )


  assert |- J e. ( TopOn ` CC )

  proof
    ccnfld
    ctps
    wcel
    cJ
    cc
    ctopon
    cfv
    wcel
    cnfldtps
    cc
    cJ
    ccnfld
    cnfldbas
    cnfldtopn.1
    istps
    mpbi
end
