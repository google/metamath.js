include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cmopn.mm"
include "cfv.mm"
include "cvv.mm"
include "wcel.mm"
include "ccnfld.mm"
include "cts.mm"
include "wceq.mm"
include "fvex.mm"
include "c1.mm"
include "c3.mm"
include "cdc.mm"
include "cop.mm"
include "cnfldstr.mm"
include "tsetid.mm"
include "cnx.mm"
include "csn.mm"
include "cple.mm"
include "cle.mm"
include "cds.mm"
include "ctp.mm"
include "snsstp1.mm"
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

theorem cnfldtset



  assert |- ( MetOpen ` ( abs o. - ) ) = ( TopSet ` CCfld )

  proof
    cabs
    cmin
    ccom
    #
    cmopn
    cfv
    #
    cvv
    wcel
    @1
    ccnfld
    cts
    cfv
    wceq
    @0
    cmopn
    fvex
    @1
    ccnfld
    cts
    cvv
    c1
    c1
    c3
    cdc
    cop
    cnfldstr
    tsetid
    cnx
    cts
    cfv
    @1
    cop
    #
    csn
    @2
    cnx
    cple
    cfv
    cle
    cop
    #
    cnx
    cds
    cfv
    @0
    cop
    #
    ctp
    #
    ccnfld
    @2
    @3
    @4
    snsstp1
    @5
    @5
    cnx
    cunif
    cfv
    @0
    cmetu
    cfv
    cop
    csn
    #
    cun
    #
    ccnfld
    @5
    @6
    ssun1
    @7
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
    @7
    cun
    ccnfld
    @7
    @8
    ssun2
    df-cnfld
    sseqtr4i
    sstri
    sstri
    strfv
    ax-mp
end
