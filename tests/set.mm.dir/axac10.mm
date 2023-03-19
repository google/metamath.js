include "wac.mm"
include "cen.mm"
include "con0.mm"
include "cima.mm"
include "cvv.mm"
include "wceq.mm"
include "axac3.mm"
include "dfac10b.mm"
include "mpbi.mm"

theorem axac10



  assert |- ( ~~ " On ) = _V

  proof
    wac
    cen
    con0
    cima
    cvv
    wceq
    axac3
    dfac10b
    mpbi
end
