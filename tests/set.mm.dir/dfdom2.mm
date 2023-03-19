include "cen.mm"
include "csdm.mm"
include "cun.mm"
include "cdom.mm"
include "cdif.mm"
include "df-sdom.mm"
include "uneq2i.mm"
include "uncom.mm"
include "wss.mm"
include "wceq.mm"
include "enssdom.mm"
include "undif.mm"
include "mpbi.mm"
include "3eqtr3ri.mm"

theorem dfdom2



  assert |- ~<_ = ( ~< u. ~~ )

  proof
    cen
    csdm
    cun
    cen
    cdom
    cen
    cdif
    #
    cun
    #
    csdm
    cen
    cun
    cdom
    csdm
    @0
    cen
    df-sdom
    uneq2i
    cen
    csdm
    uncom
    cen
    cdom
    wss
    @1
    cdom
    wceq
    enssdom
    cen
    cdom
    undif
    mpbi
    3eqtr3ri
end
