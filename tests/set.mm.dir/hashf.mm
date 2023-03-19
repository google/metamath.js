include "cvv.mm"
include "cn0.mm"
include "cpnf.mm"
include "csn.mm"
include "cun.mm"
include "chash.mm"
include "wf.mm"
include "cxnn0.mm"
include "hashfxnn0.mm"
include "eqid.mm"
include "df-xnn0.mm"
include "eqcomi.mm"
include "feq23i.mm"
include "mpbir.mm"

theorem hashf



  assert |- # : _V --> ( NN0 u. { +oo } )

  proof
    cvv
    cn0
    cpnf
    csn
    cun
    #
    chash
    wf
    cvv
    cxnn0
    chash
    wf
    hashfxnn0
    cvv
    @0
    cvv
    cxnn0
    chash
    cvv
    eqid
    cxnn0
    @0
    df-xnn0
    eqcomi
    feq23i
    mpbir
end
