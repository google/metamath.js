include "ccnfld.mm"
include "crrext.mm"
include "wcel.mm"
include "cnrg.mm"
include "cdr.mm"
include "wa.mm"
include "czlm.mm"
include "cfv.mm"
include "cnlm.mm"
include "cchr.mm"
include "cc0.mm"
include "wceq.mm"
include "ccusp.mm"
include "cuss.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cmetu.mm"
include "cnnrg.mm"
include "cndrng.mm"
include "pm3.2i.mm"
include "cnzh.mm"
include "crefld.mm"
include "cr.mm"
include "cress.mm"
include "co.mm"
include "df-refld.mm"
include "fveq2i.mm"
include "cofld.mm"
include "reofld.mm"
include "ofldchr.mm"
include "ax-mp.mm"
include "csubrg.mm"
include "resubdrg.mm"
include "simpli.mm"
include "subrgchr.mm"
include "3eqtr3ri.mm"
include "cnfldcusp.mm"
include "eqid.mm"
include "cnflduss.mm"
include "cc.mm"
include "cnfldbas.mm"
include "cxp.mm"
include "cres.mm"
include "cds.mm"
include "wfn.mm"
include "cme.mm"
include "wf.mm"
include "cnmet.mm"
include "metf.mm"
include "ffn.mm"
include "mp2b.mm"
include "fnresdm.mm"
include "cnfldds.mm"
include "reseq1i.mm"
include "eqtr3i.mm"
include "isrrext.mm"
include "mpbir3an.mm"

theorem cnrrext



  assert |- CCfld e. RRExt

  proof
    ccnfld
    crrext
    wcel
    ccnfld
    cnrg
    wcel
    #
    ccnfld
    cdr
    wcel
    #
    wa
    ccnfld
    czlm
    cfv
    #
    cnlm
    wcel
    #
    ccnfld
    cchr
    cfv
    #
    cc0
    wceq
    #
    wa
    ccnfld
    ccusp
    wcel
    #
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
    #
    wa
    @0
    @1
    cnnrg
    cndrng
    pm3.2i
    @3
    @5
    cnzh
    crefld
    cchr
    cfv
    #
    ccnfld
    cr
    cress
    co
    #
    cchr
    cfv
    #
    cc0
    @4
    crefld
    @11
    cchr
    df-refld
    fveq2i
    crefld
    cofld
    wcel
    @10
    cc0
    wceq
    reofld
    crefld
    ofldchr
    ax-mp
    cr
    ccnfld
    csubrg
    cfv
    wcel
    #
    @12
    @4
    wceq
    @13
    crefld
    cdr
    wcel
    resubdrg
    simpli
    cr
    ccnfld
    subrgchr
    ax-mp
    3eqtr3ri
    pm3.2i
    @6
    @9
    cnfldcusp
    @7
    @7
    eqid
    cnflduss
    pm3.2i
    cc
    @8
    ccnfld
    @2
    cnfldbas
    @8
    cc
    cc
    cxp
    #
    cres
    #
    @8
    ccnfld
    cds
    cfv
    #
    @14
    cres
    @8
    @14
    wfn
    #
    @15
    @8
    wceq
    @8
    cc
    cme
    cfv
    wcel
    @14
    cr
    @8
    wf
    @17
    cnmet
    @8
    cc
    metf
    @14
    cr
    @8
    ffn
    mp2b
    @14
    @8
    fnresdm
    ax-mp
    @8
    @16
    @14
    cnfldds
    reseq1i
    eqtr3i
    @2
    eqid
    isrrext
    mpbir3an
end
