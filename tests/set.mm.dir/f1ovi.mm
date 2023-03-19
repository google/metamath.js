include "cvv.mm"
include "cid.mm"
include "cres.mm"
include "wf1o.mm"
include "f1oi.mm"
include "wceq.mm"
include "wb.mm"
include "wrel.mm"
include "reli.mm"
include "dfrel3.mm"
include "mpbi.mm"
include "f1oeq1.mm"
include "ax-mp.mm"

theorem f1ovi



  assert |- _I : _V -1-1-onto-> _V

  proof
    cvv
    cvv
    cid
    cvv
    cres
    #
    wf1o
    #
    cvv
    cvv
    cid
    wf1o
    #
    cvv
    f1oi
    @0
    cid
    wceq
    #
    @1
    @2
    wb
    cid
    wrel
    @3
    reli
    cid
    dfrel3
    mpbi
    cvv
    cvv
    @0
    cid
    f1oeq1
    ax-mp
    mpbi
end
