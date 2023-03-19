include "cc.mm"
include "c0.mm"
include "wne.mm"
include "ccnfld.mm"
include "ccms.mm"
include "wcel.mm"
include "cuss.mm"
include "cfv.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cmetu.mm"
include "wceq.mm"
include "ccusp.mm"
include "cc0.mm"
include "0cn.mm"
include "ne0ii.mm"
include "cncms.mm"
include "eqid.mm"
include "cnflduss.mm"
include "cnfldbas.mm"
include "cxp.mm"
include "cres.mm"
include "cds.mm"
include "cr.mm"
include "wf.mm"
include "wfn.mm"
include "absf.mm"
include "subf.mm"
include "fco.mm"
include "mp2an.mm"
include "ffn.mm"
include "fnresdm.mm"
include "mp2b.mm"
include "cnfldds.mm"
include "reseq1i.mm"
include "eqtr3i.mm"
include "cmetcusp1.mm"
include "mp3an.mm"

theorem cnfldcusp



  assert |- CCfld e. CUnifSp

  proof
    cc
    c0
    wne
    ccnfld
    ccms
    wcel
    ccnfld
    cuss
    cfv
    #
    cabs
    cmin
    ccom
    #
    cmetu
    cfv
    wceq
    ccnfld
    ccusp
    wcel
    cc0
    cc
    0cn
    ne0ii
    cncms
    @0
    @0
    eqid
    #
    cnflduss
    @1
    @0
    ccnfld
    cc
    cnfldbas
    @1
    cc
    cc
    cxp
    #
    cres
    #
    @1
    ccnfld
    cds
    cfv
    #
    @3
    cres
    @3
    cr
    @1
    wf
    #
    @1
    @3
    wfn
    @4
    @1
    wceq
    cc
    cr
    cabs
    wf
    @3
    cc
    cmin
    wf
    @6
    absf
    subf
    @3
    cc
    cr
    cabs
    cmin
    fco
    mp2an
    @3
    cr
    @1
    ffn
    @3
    @1
    fnresdm
    mp2b
    @1
    @5
    @3
    cnfldds
    reseq1i
    eqtr3i
    @2
    cmetcusp1
    mp3an
end
