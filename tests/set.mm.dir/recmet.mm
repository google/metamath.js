include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cr.mm"
include "cxp.mm"
include "cres.mm"
include "cms.mm"
include "cfv.mm"
include "wcel.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "ccld.mm"
include "eqid.mm"
include "recld2.mm"
include "cc.mm"
include "wb.mm"
include "cncmet.mm"
include "cnfldtopn.mm"
include "cmetss.mm"
include "ax-mp.mm"
include "mpbir.mm"

theorem recmet



  assert |- ( ( abs o. - ) |` ( RR X. RR ) ) e. ( CMet ` RR )

  proof
    cabs
    cmin
    ccom
    #
    cr
    cr
    cxp
    cres
    cr
    cms
    cfv
    wcel
    #
    cr
    ccnfld
    ctopn
    cfv
    #
    ccld
    cfv
    wcel
    #
    @2
    @2
    eqid
    #
    recld2
    @0
    cc
    cms
    cfv
    wcel
    @1
    @3
    wb
    @0
    @0
    eqid
    cncmet
    @0
    @2
    cc
    cr
    @2
    @4
    cnfldtopn
    cmetss
    ax-mp
    mpbir
end
