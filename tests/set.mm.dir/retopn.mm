include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cr.mm"
include "crest.mm"
include "co.mm"
include "crefld.mm"
include "eqid.mm"
include "tgioo2.mm"
include "df-refld.mm"
include "resstopn.mm"
include "eqtri.mm"

theorem retopn



  assert |- ( topGen ` ran (,) ) = ( TopOpen ` RRfld )

  proof
    cioo
    crn
    ctg
    cfv
    ccnfld
    ctopn
    cfv
    #
    cr
    crest
    co
    crefld
    ctopn
    cfv
    @0
    @0
    eqid
    #
    tgioo2
    cr
    crefld
    @0
    ccnfld
    df-refld
    @1
    resstopn
    eqtri
end
