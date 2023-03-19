include "c0.mm"
include "chash.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "eqid.mm"
include "cvv.mm"
include "wcel.mm"
include "wb.mm"
include "0ex.mm"
include "hasheq0.mm"
include "ax-mp.mm"
include "mpbir.mm"

theorem hash0



  assert |- ( # ` (/) ) = 0

  proof
    c0
    chash
    cfv
    cc0
    wceq
    #
    c0
    c0
    wceq
    #
    c0
    eqid
    c0
    cvv
    wcel
    @0
    @1
    wb
    0ex
    c0
    cvv
    hasheq0
    ax-mp
    mpbir
end
