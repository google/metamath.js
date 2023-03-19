include "ccnfld.mm"
include "ccrg.mm"
include "wcel.mm"
include "cz.mm"
include "csubrg.mm"
include "cfv.mm"
include "zring.mm"
include "cncrng.mm"
include "zsubrg.mm"
include "df-zring.mm"
include "subrgcrng.mm"
include "mp2an.mm"

theorem zringcrng



  assert |- ZZring e. CRing

  proof
    ccnfld
    ccrg
    wcel
    cz
    ccnfld
    csubrg
    cfv
    wcel
    zring
    ccrg
    wcel
    cncrng
    zsubrg
    cz
    ccnfld
    zring
    df-zring
    subrgcrng
    mp2an
end
