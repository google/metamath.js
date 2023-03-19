include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cmetu.mm"
include "cfv.mm"
include "cvv.mm"
include "wcel.mm"
include "ccnfld.mm"
include "cunif.mm"
include "wceq.mm"
include "fvex.mm"
include "c1.mm"
include "c3.mm"
include "cdc.mm"
include "cop.mm"
include "cnfldstr.mm"
include "unifid.mm"
include "cnx.mm"
include "csn.mm"
include "cts.mm"
include "cmopn.mm"
include "cple.mm"
include "cle.mm"
include "cds.mm"
include "ctp.mm"
include "cun.mm"
include "ssun2.mm"
include "cbs.mm"
include "cc.mm"
include "cplusg.mm"
include "caddc.mm"
include "cmulr.mm"
include "cmul.mm"
include "cstv.mm"
include "ccj.mm"
include "df-cnfld.mm"
include "sseqtr4i.mm"
include "sstri.mm"
include "strfv.mm"
include "ax-mp.mm"

theorem cnfldunif



  assert |- ( metUnif ` ( abs o. - ) ) = ( UnifSet ` CCfld )

  proof
    cabs
    cmin
    ccom
    #
    cmetu
    cfv
    #
    cvv
    wcel
    @1
    ccnfld
    cunif
    cfv
    wceq
    @0
    cmetu
    fvex
    @1
    ccnfld
    cunif
    cvv
    c1
    c1
    c3
    cdc
    cop
    cnfldstr
    unifid
    cnx
    cunif
    cfv
    @1
    cop
    csn
    #
    cnx
    cts
    cfv
    @0
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
    @0
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
    @4
    cun
    ccnfld
    @4
    @5
    ssun2
    df-cnfld
    sseqtr4i
    sstri
    strfv
    ax-mp
end
