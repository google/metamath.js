include "cmul.mm"
include "cvv.mm"
include "wcel.mm"
include "ccnfld.mm"
include "cmulr.mm"
include "cfv.mm"
include "wceq.mm"
include "mulex.mm"
include "c1.mm"
include "c3.mm"
include "cdc.mm"
include "cop.mm"
include "cnfldstr.mm"
include "mulrid.mm"
include "cnx.mm"
include "csn.mm"
include "cbs.mm"
include "cc.mm"
include "cplusg.mm"
include "caddc.mm"
include "ctp.mm"
include "snsstp3.mm"
include "cstv.mm"
include "ccj.mm"
include "cun.mm"
include "ssun1.mm"
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
include "df-cnfld.mm"
include "sseqtr4i.mm"
include "sstri.mm"
include "strfv.mm"
include "ax-mp.mm"

theorem cnfldmul



  assert |- x. = ( .r ` CCfld )

  proof
    cmul
    cvv
    wcel
    cmul
    ccnfld
    cmulr
    cfv
    wceq
    mulex
    cmul
    ccnfld
    cmulr
    cvv
    c1
    c1
    c3
    cdc
    cop
    cnfldstr
    mulrid
    cnx
    cmulr
    cfv
    cmul
    cop
    #
    csn
    cnx
    cbs
    cfv
    cc
    cop
    #
    cnx
    cplusg
    cfv
    caddc
    cop
    #
    @0
    ctp
    #
    ccnfld
    @1
    @2
    @0
    snsstp3
    @3
    @3
    cnx
    cstv
    cfv
    ccj
    cop
    csn
    #
    cun
    #
    ccnfld
    @3
    @4
    ssun1
    @5
    @5
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
    @6
    cop
    ctp
    cnx
    cunif
    cfv
    @6
    cmetu
    cfv
    cop
    csn
    cun
    #
    cun
    ccnfld
    @5
    @7
    ssun1
    df-cnfld
    sseqtr4i
    sstri
    sstri
    strfv
    ax-mp
end
