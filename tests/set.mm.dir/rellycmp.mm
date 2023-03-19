include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cr.mm"
include "crest.mm"
include "co.mm"
include "ccmp.mm"
include "cnlly.mm"
include "eqid.mm"
include "tgioo2.mm"
include "wcel.mm"
include "ccld.mm"
include "cnllycmp.mm"
include "recld2.mm"
include "cldllycmp.mm"
include "mp2an.mm"
include "eqeltri.mm"

theorem rellycmp



  assert |- ( topGen ` ran (,) ) e. N-Locally Comp

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
    #
    ccmp
    cnlly
    #
    @0
    @0
    eqid
    #
    tgioo2
    @0
    @2
    wcel
    cr
    @0
    ccld
    cfv
    wcel
    @1
    @2
    wcel
    @0
    @3
    cnllycmp
    @0
    @3
    recld2
    cr
    @0
    cldllycmp
    mp2an
    eqeltri
end
