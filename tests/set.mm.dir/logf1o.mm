include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "clog.mm"
include "crn.mm"
include "wf1o.mm"
include "ce.mm"
include "cres.mm"
include "ccnv.mm"
include "eff1o2.mm"
include "f1ocnv.mm"
include "ax-mp.mm"
include "wceq.mm"
include "wb.mm"
include "dflog2.mm"
include "f1oeq1.mm"
include "mpbir.mm"

theorem logf1o



  assert |- log : ( CC \ { 0 } ) -1-1-onto-> ran log

  proof
    cc
    cc0
    csn
    cdif
    #
    clog
    crn
    #
    clog
    wf1o
    #
    @0
    @1
    ce
    @1
    cres
    #
    ccnv
    #
    wf1o
    #
    @1
    @0
    @3
    wf1o
    @5
    eff1o2
    @1
    @0
    @3
    f1ocnv
    ax-mp
    clog
    @4
    wceq
    @2
    @5
    wb
    dflog2
    @0
    @1
    clog
    @4
    f1oeq1
    ax-mp
    mpbir
end
