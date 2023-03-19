include "ce.mm"
include "clog.mm"
include "crn.mm"
include "cres.mm"
include "ccnv.mm"
include "cr.mm"
include "cima.mm"
include "crp.mm"
include "df-ima.mm"
include "wss.mm"
include "wceq.mm"
include "cv.mm"
include "relogrn.mm"
include "ssriv.mm"
include "resabs1.mm"
include "ax-mp.mm"
include "rneqi.mm"
include "wfn.mm"
include "wfun.mm"
include "wf1o.mm"
include "w3a.mm"
include "reeff1o.mm"
include "dff1o2.mm"
include "mpbi.mm"
include "simp3i.mm"
include "3eqtri.mm"
include "reseq2i.mm"
include "cnveqi.mm"
include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "logf1o.mm"
include "f1ofun.mm"
include "dflog2.mm"
include "funeqi.mm"
include "funcnvres.mm"
include "eqtr3i.mm"
include "reseq1i.mm"
include "3eqtr4ri.mm"

theorem dfrelog
  let vx: setvar x


  assert |- ( log |` RR+ ) = `' ( exp |` RR )

  proof
    ce
    clog
    crn
    #
    cres
    #
    ccnv
    #
    @1
    cr
    cima
    #
    cres
    #
    @2
    crp
    cres
    ce
    cr
    cres
    #
    ccnv
    #
    clog
    crp
    cres
    @3
    crp
    @2
    @3
    @1
    cr
    cres
    #
    crn
    @5
    crn
    #
    crp
    @1
    cr
    df-ima
    @7
    @5
    cr
    @0
    wss
    @7
    @5
    wceq
    vx
    cr
    @0
    vx
    cv
    relogrn
    ssriv
    ce
    cr
    @0
    resabs1
    ax-mp
    #
    rneqi
    @5
    cr
    wfn
    #
    @6
    wfun
    #
    @8
    crp
    wceq
    #
    cr
    crp
    @5
    wf1o
    @10
    @11
    @12
    w3a
    reeff1o
    cr
    crp
    @5
    dff1o2
    mpbi
    simp3i
    3eqtri
    reseq2i
    @7
    ccnv
    #
    @6
    @4
    @7
    @5
    @9
    cnveqi
    @2
    wfun
    #
    @13
    @4
    wceq
    clog
    wfun
    #
    @14
    cc
    cc0
    csn
    cdif
    #
    @0
    clog
    wf1o
    @15
    logf1o
    @16
    @0
    clog
    f1ofun
    ax-mp
    clog
    @2
    dflog2
    funeqi
    mpbi
    cr
    @1
    funcnvres
    ax-mp
    eqtr3i
    clog
    @2
    crp
    dflog2
    reseq1i
    3eqtr4ri
end
