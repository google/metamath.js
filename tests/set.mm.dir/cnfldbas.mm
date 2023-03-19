include "cc.mm"
include "cvv.mm"
include "wcel.mm"
include "ccnfld.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "cnex.mm"
include "c1.mm"
include "c3.mm"
include "cdc.mm"
include "cop.mm"
include "cnfldstr.mm"
include "baseid.mm"
include "cnx.mm"
include "csn.mm"
include "cplusg.mm"
include "caddc.mm"
include "cmulr.mm"
include "cmul.mm"
include "ctp.mm"
include "snsstp1.mm"
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

theorem cnfldbas



  assert |- CC = ( Base ` CCfld )

  proof
    cc
    cvv
    wcel
    cc
    ccnfld
    cbs
    cfv
    wceq
    cnex
    cc
    ccnfld
    cbs
    cvv
    c1
    c1
    c3
    cdc
    cop
    cnfldstr
    baseid
    cnx
    cbs
    cfv
    cc
    cop
    #
    csn
    @0
    cnx
    cplusg
    cfv
    caddc
    cop
    #
    cnx
    cmulr
    cfv
    cmul
    cop
    #
    ctp
    #
    ccnfld
    @0
    @1
    @2
    snsstp1
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
