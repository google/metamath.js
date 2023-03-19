include "cle.mm"
include "cxr.mm"
include "cxp.mm"
include "clt.mm"
include "ccnv.mm"
include "cdif.mm"
include "df-le.mm"
include "difss.mm"
include "eqsstri.mm"

theorem lerelxr



  assert |- <_ C_ ( RR* X. RR* )

  proof
    cle
    cxr
    cxr
    cxp
    #
    clt
    ccnv
    #
    cdif
    @0
    df-le
    @0
    @1
    difss
    eqsstri
end
