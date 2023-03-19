include "crefld.mm"
include "cuss.mm"
include "cfv.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cmetu.mm"
include "cr.mm"
include "cxp.mm"
include "crest.mm"
include "co.mm"
include "cres.mm"
include "cds.mm"
include "ccnfld.mm"
include "cress.mm"
include "df-refld.mm"
include "fveq2i.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "reex.mm"
include "ressuss.mm"
include "ax-mp.mm"
include "eqid.mm"
include "cnflduss.mm"
include "oveq1i.mm"
include "3eqtri.mm"
include "c0.mm"
include "wne.mm"
include "cc.mm"
include "cpsmet.mm"
include "wss.mm"
include "cc0.mm"
include "0re.mm"
include "ne0ii.mm"
include "cxmt.mm"
include "cnxmet.mm"
include "xmetpsmet.mm"
include "ax-resscn.mm"
include "restmetu.mm"
include "mp3an.mm"
include "reds.mm"
include "reseq1i.mm"

theorem reust



  assert |- ( UnifSt ` RRfld ) = ( metUnif ` ( ( dist ` RRfld ) |` ( RR X. RR ) ) )

  proof
    crefld
    cuss
    cfv
    #
    cabs
    cmin
    ccom
    #
    cmetu
    cfv
    #
    cr
    cr
    cxp
    #
    crest
    co
    #
    @1
    @3
    cres
    #
    cmetu
    cfv
    #
    crefld
    cds
    cfv
    #
    @3
    cres
    #
    cmetu
    cfv
    @0
    ccnfld
    cr
    cress
    co
    #
    cuss
    cfv
    #
    ccnfld
    cuss
    cfv
    #
    @3
    crest
    co
    #
    @4
    crefld
    @9
    cuss
    df-refld
    fveq2i
    cr
    cvv
    wcel
    @10
    @12
    wceq
    reex
    cr
    cvv
    ccnfld
    ressuss
    ax-mp
    @11
    @2
    @3
    crest
    @11
    @11
    eqid
    cnflduss
    oveq1i
    3eqtri
    cr
    c0
    wne
    @1
    cc
    cpsmet
    cfv
    wcel
    #
    cr
    cc
    wss
    @4
    @6
    wceq
    cc0
    cr
    0re
    ne0ii
    @1
    cc
    cxmt
    cfv
    wcel
    @13
    cnxmet
    @1
    cc
    xmetpsmet
    ax-mp
    ax-resscn
    cr
    @1
    cc
    restmetu
    mp3an
    @5
    @8
    cmetu
    @1
    @7
    @3
    reds
    reseq1i
    fveq2i
    3eqtri
end
