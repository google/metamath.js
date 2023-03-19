include "caddc.mm"
include "cvv.mm"
include "wcel.mm"
include "ccnfld.mm"
include "cplusg.mm"
include "cfv.mm"
include "wceq.mm"
include "addex.mm"
include "c1.mm"
include "c3.mm"
include "cdc.mm"
include "cop.mm"
include "cnfldstr.mm"
include "plusgid.mm"
include "cnx.mm"
include "csn.mm"
include "cbs.mm"
include "cc.mm"
include "cmulr.mm"
include "cmul.mm"
include "ctp.mm"
include "snsstp2.mm"
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

theorem cnfldadd



  assert |- + = ( +g ` CCfld )

  proof
    caddc
    cvv
    wcel
    caddc
    ccnfld
    cplusg
    cfv
    wceq
    addex
    caddc
    ccnfld
    cplusg
    cvv
    c1
    c1
    c3
    cdc
    cop
    cnfldstr
    plusgid
    cnx
    cplusg
    cfv
    caddc
    cop
    #
    csn
    cnx
    cbs
    cfv
    cc
    cop
    #
    @0
    cnx
    cmulr
    cfv
    cmul
    cop
    #
    ctp
    #
    ccnfld
    @1
    @0
    @2
    snsstp2
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
