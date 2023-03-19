include "ccnfld.mm"
include "ccms.mm"
include "wcel.mm"
include "cmt.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cc.mm"
include "cms.mm"
include "cfv.mm"
include "cnfldms.mm"
include "eqid.mm"
include "cncmet.mm"
include "cnfldbas.mm"
include "cxp.mm"
include "cres.mm"
include "cds.mm"
include "cr.mm"
include "wf.mm"
include "wfn.mm"
include "wceq.mm"
include "cme.mm"
include "cnmet.mm"
include "metf.mm"
include "ax-mp.mm"
include "ffn.mm"
include "fnresdm.mm"
include "mp2b.mm"
include "cnfldds.mm"
include "reseq1i.mm"
include "eqtr3i.mm"
include "iscms.mm"
include "mpbir2an.mm"

theorem cncms



  assert |- CCfld e. CMetSp

  proof
    ccnfld
    ccms
    wcel
    ccnfld
    cmt
    wcel
    cabs
    cmin
    ccom
    #
    cc
    cms
    cfv
    wcel
    cnfldms
    @0
    @0
    eqid
    cncmet
    @0
    ccnfld
    cc
    cnfldbas
    @0
    cc
    cc
    cxp
    #
    cres
    #
    @0
    ccnfld
    cds
    cfv
    #
    @1
    cres
    @1
    cr
    @0
    wf
    #
    @0
    @1
    wfn
    @2
    @0
    wceq
    @0
    cc
    cme
    cfv
    wcel
    @4
    cnmet
    @0
    cc
    metf
    ax-mp
    @1
    cr
    @0
    ffn
    @1
    @0
    fnresdm
    mp2b
    @0
    @3
    @1
    cnfldds
    reseq1i
    eqtr3i
    iscms
    mpbir2an
end
