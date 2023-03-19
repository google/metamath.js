include "ccnfld.mm"
include "cmt.mm"
include "wcel.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cc.mm"
include "cme.mm"
include "cfv.mm"
include "cmopn.mm"
include "wceq.mm"
include "cnmet.mm"
include "eqid.mm"
include "cxmt.mm"
include "ctopon.mm"
include "ctopn.mm"
include "cnxmet.mm"
include "mopntopon.mm"
include "cnfldbas.mm"
include "cnfldtset.mm"
include "topontopn.mm"
include "mp2b.mm"
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
include "cnfldds.mm"
include "reseq1i.mm"
include "eqtr3i.mm"
include "isms2.mm"
include "mpbir2an.mm"

theorem cnfldms



  assert |- CCfld e. MetSp

  proof
    ccnfld
    cmt
    wcel
    cabs
    cmin
    ccom
    #
    cc
    cme
    cfv
    wcel
    @0
    cmopn
    cfv
    #
    @1
    wceq
    cnmet
    @1
    eqid
    #
    @0
    @1
    ccnfld
    cc
    @0
    cc
    cxmt
    cfv
    wcel
    @1
    cc
    ctopon
    cfv
    wcel
    @1
    ccnfld
    ctopn
    cfv
    wceq
    cnxmet
    @0
    @1
    cc
    @2
    mopntopon
    cc
    @1
    ccnfld
    cnfldbas
    cnfldtset
    topontopn
    mp2b
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
    @3
    cres
    @3
    cr
    @0
    wf
    #
    @0
    @3
    wfn
    @4
    @0
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
    @0
    ffn
    @3
    @0
    fnresdm
    mp2b
    @0
    @5
    @3
    cnfldds
    reseq1i
    eqtr3i
    isms2
    mpbir2an
end
