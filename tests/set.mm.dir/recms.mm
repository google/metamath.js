include "crefld.mm"
include "ccms.mm"
include "wcel.mm"
include "cr.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "ccld.mm"
include "eqid.mm"
include "recld2.mm"
include "cc.mm"
include "wss.mm"
include "wb.mm"
include "cncms.mm"
include "ax-resscn.mm"
include "df-refld.mm"
include "cnfldbas.mm"
include "cmsss.mm"
include "mp2an.mm"
include "mpbir.mm"

theorem recms



  assert |- RRfld e. CMetSp

  proof
    crefld
    ccms
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
    @1
    @1
    eqid
    #
    recld2
    ccnfld
    ccms
    wcel
    cr
    cc
    wss
    @0
    @2
    wb
    cncms
    ax-resscn
    cr
    @1
    crefld
    ccnfld
    cc
    df-refld
    cnfldbas
    @3
    cmsss
    mp2an
    mpbir
end
