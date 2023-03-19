include "cnpi.mm"
include "com.mm"
include "omex.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "df-ni.mm"
include "difss.mm"
include "eqsstri.mm"
include "ssexi.mm"

theorem niex



  assert |- N. e. _V

  proof
    cnpi
    com
    omex
    cnpi
    com
    c0
    csn
    #
    cdif
    com
    df-ni
    com
    @0
    difss
    eqsstri
    ssexi
end
