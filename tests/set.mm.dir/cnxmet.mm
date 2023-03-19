include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cc.mm"
include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "cxmt.mm"
include "cnmet.mm"
include "metxmet.mm"
include "ax-mp.mm"

theorem cnxmet
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( abs o. - ) e. ( *Met ` CC )

  proof
    cabs
    cmin
    ccom
    #
    cc
    cme
    cfv
    wcel
    @0
    cc
    cxmt
    cfv
    wcel
    cnmet
    @0
    cc
    metxmet
    ax-mp
end
