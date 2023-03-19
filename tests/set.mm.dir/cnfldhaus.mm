include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cc.mm"
include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cha.mm"
include "cnxmet.mm"
include "cnfldtopn.mm"
include "methaus.mm"
include "ax-mp.mm"

theorem cnfldhaus
  let cJ: class J
  assume cnfldtopn.1: |- J = ( TopOpen ` CCfld )


  assert |- J e. Haus

  proof
    cabs
    cmin
    ccom
    #
    cc
    cxmt
    cfv
    wcel
    cJ
    cha
    wcel
    cnxmet
    @0
    cJ
    cc
    cJ
    cnfldtopn.1
    cnfldtopn
    methaus
    ax-mp
end
