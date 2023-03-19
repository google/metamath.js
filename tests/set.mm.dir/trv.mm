include "cvv.mm"
include "wtr.mm"
include "cuni.mm"
include "wss.mm"
include "ssv.mm"
include "df-tr.mm"
include "mpbir.mm"

theorem trv



  assert |- Tr _V

  proof
    cvv
    wtr
    cvv
    cuni
    #
    cvv
    wss
    @0
    ssv
    cvv
    df-tr
    mpbir
end
