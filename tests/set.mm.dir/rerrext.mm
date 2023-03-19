include "crefld.mm"
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
include "cds.mm"
include "cr.mm"
include "cxp.mm"
include "cres.mm"
include "cmetu.mm"
include "ccnfld.mm"
include "csubrg.mm"
include "cnnrg.mm"
include "resubdrg.mm"
include "simpli.mm"
include "df-refld.mm"
include "subrgnrg.mm"
include "mp2an.mm"
include "simpri.mm"
include "pm3.2i.mm"
include "rezh.mm"
include "cofld.mm"
include "reofld.mm"
include "ofldchr.mm"
include "ax-mp.mm"
include "recusp.mm"
include "reust.mm"
include "rebase.mm"
include "eqid.mm"
include "isrrext.mm"
include "mpbir3an.mm"

theorem rerrext



  assert |- RRfld e. RRExt

  proof
    crefld
    crrext
    wcel
    crefld
    cnrg
    wcel
    #
    crefld
    cdr
    wcel
    #
    wa
    crefld
    czlm
    cfv
    #
    cnlm
    wcel
    #
    crefld
    cchr
    cfv
    cc0
    wceq
    #
    wa
    crefld
    ccusp
    wcel
    #
    crefld
    cuss
    cfv
    crefld
    cds
    cfv
    cr
    cr
    cxp
    cres
    #
    cmetu
    cfv
    wceq
    #
    wa
    @0
    @1
    ccnfld
    cnrg
    wcel
    cr
    ccnfld
    csubrg
    cfv
    wcel
    #
    @0
    cnnrg
    @8
    @1
    resubdrg
    simpli
    cr
    ccnfld
    crefld
    df-refld
    subrgnrg
    mp2an
    @8
    @1
    resubdrg
    simpri
    pm3.2i
    @3
    @4
    rezh
    crefld
    cofld
    wcel
    @4
    reofld
    crefld
    ofldchr
    ax-mp
    pm3.2i
    @5
    @7
    recusp
    reust
    pm3.2i
    cr
    @6
    crefld
    @2
    rebase
    @6
    eqid
    @2
    eqid
    isrrext
    mpbir3an
end
