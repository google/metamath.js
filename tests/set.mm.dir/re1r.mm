include "cr.mm"
include "ccnfld.mm"
include "csubrg.mm"
include "cfv.mm"
include "wcel.mm"
include "c1.mm"
include "crefld.mm"
include "cur.mm"
include "wceq.mm"
include "cdr.mm"
include "resubdrg.mm"
include "simpli.mm"
include "df-refld.mm"
include "cnfld1.mm"
include "subrg1.mm"
include "ax-mp.mm"

theorem re1r



  assert |- 1 = ( 1r ` RRfld )

  proof
    cr
    ccnfld
    csubrg
    cfv
    wcel
    #
    c1
    crefld
    cur
    cfv
    wceq
    @0
    crefld
    cdr
    wcel
    resubdrg
    simpli
    cr
    ccnfld
    crefld
    c1
    df-refld
    cnfld1
    subrg1
    ax-mp
end
