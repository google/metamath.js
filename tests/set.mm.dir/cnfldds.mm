include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cvv.mm"
include "wcel.mm"
include "ccnfld.mm"
include "cds.mm"
include "cfv.mm"
include "wceq.mm"
include "cc.mm"
include "cxp.mm"
include "cr.mm"
include "wf.mm"
include "absf.mm"
include "subf.mm"
include "fco.mm"
include "mp2an.mm"
include "cnex.mm"
include "xpex.mm"
include "reex.mm"
include "fex2.mm"
include "mp3an.mm"
include "c1.mm"
include "c3.mm"
include "cdc.mm"
include "cop.mm"
include "cnfldstr.mm"
include "dsid.mm"
include "cnx.mm"
include "csn.mm"
include "cts.mm"
include "cmopn.mm"
include "cple.mm"
include "cle.mm"
include "ctp.mm"
include "snsstp3.mm"
include "cunif.mm"
include "cmetu.mm"
include "cun.mm"
include "ssun1.mm"
include "cbs.mm"
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

theorem cnfldds



  assert |- ( abs o. - ) = ( dist ` CCfld )

  proof
    cabs
    cmin
    ccom
    #
    cvv
    wcel
    #
    @0
    ccnfld
    cds
    cfv
    wceq
    cc
    cc
    cxp
    #
    cr
    @0
    wf
    #
    @2
    cvv
    wcel
    cr
    cvv
    wcel
    @1
    cc
    cr
    cabs
    wf
    @2
    cc
    cmin
    wf
    @3
    absf
    subf
    @2
    cc
    cr
    cabs
    cmin
    fco
    mp2an
    cc
    cc
    cnex
    cnex
    xpex
    reex
    @2
    cr
    @0
    cvv
    cvv
    fex2
    mp3an
    @0
    ccnfld
    cds
    cvv
    c1
    c1
    c3
    cdc
    cop
    cnfldstr
    dsid
    cnx
    cds
    cfv
    @0
    cop
    #
    csn
    cnx
    cts
    cfv
    @0
    cmopn
    cfv
    cop
    #
    cnx
    cple
    cfv
    cle
    cop
    #
    @4
    ctp
    #
    ccnfld
    @5
    @6
    @4
    snsstp3
    @7
    @7
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
    @7
    @8
    ssun1
    @9
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
    @9
    cun
    ccnfld
    @9
    @10
    ssun2
    df-cnfld
    sseqtr4i
    sstri
    sstri
    strfv
    ax-mp
end
