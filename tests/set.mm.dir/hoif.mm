include "chil.mm"
include "chio.mm"
include "wf1o.mm"
include "cid.mm"
include "cres.mm"
include "f1oi.mm"
include "wceq.mm"
include "wb.mm"
include "dfiop2.mm"
include "f1oeq1.mm"
include "ax-mp.mm"
include "mpbir.mm"

theorem hoif



  assert |- Iop : ~H -1-1-onto-> ~H

  proof
    chil
    chil
    chio
    wf1o
    #
    chil
    chil
    cid
    chil
    cres
    #
    wf1o
    #
    chil
    f1oi
    chio
    @1
    wceq
    @0
    @2
    wb
    dfiop2
    chil
    chil
    chio
    @1
    f1oeq1
    ax-mp
    mpbir
end
