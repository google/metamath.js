include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "cq.mm"
include "crest.mm"
include "co.mm"
include "crefld.mm"
include "ctopn.mm"
include "ccnfld.mm"
include "cress.mm"
include "retopn.mm"
include "oveq1i.mm"
include "cr.mm"
include "df-refld.mm"
include "cvv.mm"
include "wcel.mm"
include "wss.mm"
include "wceq.mm"
include "reex.mm"
include "qssre.mm"
include "ressabs.mm"
include "mp2an.mm"
include "eqtr2i.mm"
include "resstopn.mm"
include "eqtr3i.mm"

theorem qqtopn



  assert |- ( ( TopOpen ` RRfld ) |`t QQ ) = ( TopOpen ` ( CCfld |`s QQ ) )

  proof
    cioo
    crn
    ctg
    cfv
    #
    cq
    crest
    co
    crefld
    ctopn
    cfv
    #
    cq
    crest
    co
    ccnfld
    cq
    cress
    co
    #
    ctopn
    cfv
    @0
    @1
    cq
    crest
    retopn
    oveq1i
    cq
    @2
    @0
    crefld
    crefld
    cq
    cress
    co
    ccnfld
    cr
    cress
    co
    #
    cq
    cress
    co
    #
    @2
    crefld
    @3
    cq
    cress
    df-refld
    oveq1i
    cr
    cvv
    wcel
    cq
    cr
    wss
    @4
    @2
    wceq
    reex
    qssre
    cr
    cq
    ccnfld
    cvv
    ressabs
    mp2an
    eqtr2i
    retopn
    resstopn
    eqtr3i
end
