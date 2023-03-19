include "crp.mm"
include "cr.mm"
include "clog.mm"
include "cres.mm"
include "wf1o.mm"
include "ce.mm"
include "crn.mm"
include "ccnv.mm"
include "wfun.mm"
include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "eff1o2.mm"
include "wfo.mm"
include "dff1o3.mm"
include "simprbi.mm"
include "ax-mp.mm"
include "reeff1o.mm"
include "wss.mm"
include "wceq.mm"
include "wb.mm"
include "cv.mm"
include "relogrn.mm"
include "ssriv.mm"
include "resabs1.mm"
include "f1oeq1.mm"
include "mp2b.mm"
include "mpbir.mm"
include "f1orescnv.mm"
include "mp2an.mm"
include "dflog2.mm"
include "reseq1.mm"

theorem relogf1o
  let vx: setvar x


  assert |- ( log |` RR+ ) : RR+ -1-1-onto-> RR

  proof
    crp
    cr
    clog
    crp
    cres
    #
    wf1o
    #
    crp
    cr
    ce
    clog
    crn
    #
    cres
    #
    ccnv
    #
    crp
    cres
    #
    wf1o
    #
    @4
    wfun
    #
    cr
    crp
    @3
    cr
    cres
    #
    wf1o
    #
    @6
    @2
    cc
    cc0
    csn
    cdif
    #
    @3
    wf1o
    #
    @7
    eff1o2
    @11
    @2
    @10
    @3
    wfo
    @7
    @2
    @10
    @3
    dff1o3
    simprbi
    ax-mp
    @9
    cr
    crp
    ce
    cr
    cres
    #
    wf1o
    #
    reeff1o
    cr
    @2
    wss
    @8
    @12
    wceq
    @9
    @13
    wb
    vx
    cr
    @2
    vx
    cv
    relogrn
    ssriv
    ce
    cr
    @2
    resabs1
    cr
    crp
    @8
    @12
    f1oeq1
    mp2b
    mpbir
    crp
    cr
    @3
    f1orescnv
    mp2an
    clog
    @4
    wceq
    @0
    @5
    wceq
    @1
    @6
    wb
    dflog2
    clog
    @4
    crp
    reseq1
    crp
    cr
    @0
    @5
    f1oeq1
    mp2b
    mpbir
end
