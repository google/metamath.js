include "cle.mm"
include "ctsr.mm"
include "wcel.mm"
include "ccnfld.mm"
include "cple.mm"
include "cfv.mm"
include "wceq.mm"
include "letsr.mm"
include "c1.mm"
include "c3.mm"
include "cdc.mm"
include "cop.mm"
include "cnfldstr.mm"
include "pleid.mm"
include "cnx.mm"
include "csn.mm"
include "cts.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cmopn.mm"
include "cds.mm"
include "ctp.mm"
include "snsstp2.mm"
include "cunif.mm"
include "cmetu.mm"
include "cun.mm"
include "ssun1.mm"
include "cbs.mm"
include "cc.mm"
include "cplusg.mm"
include "caddc.mm"
include "cmulr.mm"
include "cmul.mm"
include "cstv.mm"
include "ccj.mm"
include "ssun2.mm"
include "df-cnfld.mm"
include "sseqtr4i.mm"
include "sstri.mm"
include "strfv.mm"
include "ax-mp.mm"

theorem cnfldle



  assert |- <_ = ( le ` CCfld )

  proof
    cle
    ctsr
    wcel
    cle
    ccnfld
    cple
    cfv
    wceq
    letsr
    cle
    ccnfld
    cple
    ctsr
    c1
    c1
    c3
    cdc
    cop
    cnfldstr
    pleid
    cnx
    cple
    cfv
    cle
    cop
    #
    csn
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
    #
    @0
    cnx
    cds
    cfv
    @1
    cop
    #
    ctp
    #
    ccnfld
    @2
    @0
    @3
    snsstp2
    @4
    @4
    cnx
    cunif
    cfv
    @1
    cmetu
    cfv
    cop
    csn
    #
    cun
    #
    ccnfld
    @4
    @5
    ssun1
    @6
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
    cnx
    cstv
    cfv
    ccj
    cop
    csn
    cun
    #
    @6
    cun
    ccnfld
    @6
    @7
    ssun2
    df-cnfld
    sseqtr4i
    sstri
    sstri
    strfv
    ax-mp
end
