include "cdom.mm"
include "wrel.mm"
include "csdm.mm"
include "reldom.mm"
include "cen.mm"
include "cdif.mm"
include "reldif.mm"
include "df-sdom.mm"
include "releqi.mm"
include "sylibr.mm"
include "ax-mp.mm"

theorem relsdom



  assert |- Rel ~<

  proof
    cdom
    wrel
    #
    csdm
    wrel
    #
    reldom
    @0
    cdom
    cen
    cdif
    #
    wrel
    @1
    cdom
    cen
    reldif
    csdm
    @2
    df-sdom
    releqi
    sylibr
    ax-mp
end
