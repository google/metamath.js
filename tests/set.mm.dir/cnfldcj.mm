include "ccj.mm"
include "cvv.mm"
include "wcel.mm"
include "ccnfld.mm"
include "cstv.mm"
include "cfv.mm"
include "wceq.mm"
include "cc.mm"
include "wf.mm"
include "cjf.mm"
include "cnex.mm"
include "fex2.mm"
include "mp3an.mm"
include "c1.mm"
include "c3.mm"
include "cdc.mm"
include "cop.mm"
include "cnfldstr.mm"
include "starvid.mm"
include "cnx.mm"
include "csn.mm"
include "cbs.mm"
include "cplusg.mm"
include "caddc.mm"
include "cmulr.mm"
include "cmul.mm"
include "ctp.mm"
include "cun.mm"
include "ssun2.mm"
include "cts.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cmopn.mm"
include "cple.mm"
include "cle.mm"
include "cds.mm"
include "cunif.mm"
include "cmetu.mm"
include "ssun1.mm"
include "df-cnfld.mm"
include "sseqtr4i.mm"
include "sstri.mm"
include "strfv.mm"
include "ax-mp.mm"

theorem cnfldcj



  assert |- * = ( *r ` CCfld )

  proof
    ccj
    cvv
    wcel
    #
    ccj
    ccnfld
    cstv
    cfv
    wceq
    cc
    cc
    ccj
    wf
    cc
    cvv
    wcel
    #
    @1
    @0
    cjf
    cnex
    cnex
    cc
    cc
    ccj
    cvv
    cvv
    fex2
    mp3an
    ccj
    ccnfld
    cstv
    cvv
    c1
    c1
    c3
    cdc
    cop
    cnfldstr
    starvid
    cnx
    cstv
    cfv
    ccj
    cop
    csn
    #
    cnx
    cbs
    cfv
    cc
    cop
    cnx
    cplusg
    cfv
    caddc
    cop
    cnx
    cmulr
    cfv
    cmul
    cop
    ctp
    #
    @2
    cun
    #
    ccnfld
    @2
    @3
    ssun2
    @4
    @4
    cnx
    cts
    cfv
    cabs
    cmin
    ccom
    #
    cmopn
    cfv
    cop
    cnx
    cple
    cfv
    cle
    cop
    cnx
    cds
    cfv
    @5
    cop
    ctp
    cnx
    cunif
    cfv
    @5
    cmetu
    cfv
    cop
    csn
    cun
    #
    cun
    ccnfld
    @4
    @6
    ssun1
    df-cnfld
    sseqtr4i
    sstri
    strfv
    ax-mp
end
