include "wac.mm"
include "ccrd.mm"
include "cdm.mm"
include "cvv.mm"
include "wceq.mm"
include "axac3.mm"
include "dfac10.mm"
include "mpbi.mm"

theorem cardeqv



  assert |- dom card = _V

  proof
    wac
    ccrd
    cdm
    cvv
    wceq
    axac3
    dfac10
    mpbi
end
