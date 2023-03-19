include "cz.mm"
include "ccnfld.mm"
include "csubrg.mm"
include "cfv.mm"
include "wcel.mm"
include "c1.mm"
include "zring.mm"
include "cur.mm"
include "wceq.mm"
include "zsubrg.mm"
include "df-zring.mm"
include "cnfld1.mm"
include "subrg1.mm"
include "ax-mp.mm"

theorem zring1



  assert |- 1 = ( 1r ` ZZring )

  proof
    cz
    ccnfld
    csubrg
    cfv
    wcel
    c1
    zring
    cur
    cfv
    wceq
    zsubrg
    cz
    ccnfld
    zring
    c1
    df-zring
    cnfld1
    subrg1
    ax-mp
end
