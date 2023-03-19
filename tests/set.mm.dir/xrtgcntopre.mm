include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "cle.mm"
include "cordt.mm"
include "cr.mm"
include "crest.mm"
include "co.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "eqid.mm"
include "xrtgioo.mm"
include "tgioo2.mm"
include "eqtr3i.mm"

theorem xrtgcntopre



  assert |- ( ( ordTop ` <_ ) |`t RR ) = ( ( TopOpen ` CCfld ) |`t RR )

  proof
    cioo
    crn
    ctg
    cfv
    cle
    cordt
    cfv
    cr
    crest
    co
    #
    ccnfld
    ctopn
    cfv
    #
    cr
    crest
    co
    @0
    @0
    eqid
    xrtgioo
    @1
    @1
    eqid
    tgioo2
    eqtr3i
end
