include "crefld.mm"
include "cfield.mm"
include "wcel.mm"
include "cdr.mm"
include "ccrg.mm"
include "cr.mm"
include "ccnfld.mm"
include "csubrg.mm"
include "cfv.mm"
include "resubdrg.mm"
include "simpri.mm"
include "cress.mm"
include "co.mm"
include "df-refld.mm"
include "cncrng.mm"
include "simpli.mm"
include "eqid.mm"
include "subrgcrng.mm"
include "mp2an.mm"
include "eqeltri.mm"
include "isfld.mm"
include "mpbir2an.mm"

theorem refld



  assert |- RRfld e. Field

  proof
    crefld
    cfield
    wcel
    crefld
    cdr
    wcel
    #
    crefld
    ccrg
    wcel
    cr
    ccnfld
    csubrg
    cfv
    wcel
    #
    @0
    resubdrg
    simpri
    crefld
    ccnfld
    cr
    cress
    co
    #
    ccrg
    df-refld
    ccnfld
    ccrg
    wcel
    @1
    @2
    ccrg
    wcel
    cncrng
    @1
    @0
    resubdrg
    simpli
    cr
    ccnfld
    @2
    @2
    eqid
    subrgcrng
    mp2an
    eqeltri
    crefld
    isfld
    mpbir2an
end
