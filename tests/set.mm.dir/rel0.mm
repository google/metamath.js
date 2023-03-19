include "c0.mm"
include "wrel.mm"
include "cvv.mm"
include "cxp.mm"
include "wss.mm"
include "0ss.mm"
include "df-rel.mm"
include "mpbir.mm"

theorem rel0



  assert |- Rel (/)

  proof
    c0
    wrel
    c0
    cvv
    cvv
    cxp
    #
    wss
    @0
    0ss
    c0
    df-rel
    mpbir
end
