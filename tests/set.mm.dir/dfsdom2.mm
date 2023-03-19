include "csdm.mm"
include "cdom.mm"
include "cen.mm"
include "cdif.mm"
include "ccnv.mm"
include "cin.mm"
include "df-sdom.mm"
include "sbthcl.mm"
include "difeq2i.mm"
include "difin.mm"
include "3eqtri.mm"

theorem dfsdom2



  assert |- ~< = ( ~<_ \ `' ~<_ )

  proof
    csdm
    cdom
    cen
    cdif
    cdom
    cdom
    cdom
    ccnv
    #
    cin
    #
    cdif
    cdom
    @0
    cdif
    df-sdom
    cen
    @1
    cdom
    sbthcl
    difeq2i
    cdom
    @0
    difin
    3eqtri
end
