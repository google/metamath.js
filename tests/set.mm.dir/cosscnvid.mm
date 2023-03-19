include "cid.mm"
include "ccnv.mm"
include "ccoss.mm"
include "cnvi.mm"
include "cosseqi.mm"
include "cossid.mm"
include "eqtri.mm"

theorem cosscnvid



  assert |- ,~ `' _I = _I

  proof
    cid
    ccnv
    #
    ccoss
    cid
    ccoss
    cid
    @0
    cid
    cnvi
    cosseqi
    cossid
    eqtri
end
