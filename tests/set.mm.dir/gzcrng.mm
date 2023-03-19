include "ccnfld.mm"
include "ccrg.mm"
include "wcel.mm"
include "cgz.mm"
include "csubrg.mm"
include "cfv.mm"
include "cress.mm"
include "co.mm"
include "cncrng.mm"
include "gzsubrg.mm"
include "eqid.mm"
include "subrgcrng.mm"
include "mp2an.mm"

theorem gzcrng



  assert |- ( CCfld |`s Z[i] ) e. CRing

  proof
    ccnfld
    ccrg
    wcel
    cgz
    ccnfld
    csubrg
    cfv
    wcel
    ccnfld
    cgz
    cress
    co
    #
    ccrg
    wcel
    cncrng
    gzsubrg
    cgz
    ccnfld
    @0
    @0
    eqid
    subrgcrng
    mp2an
end
