include "ccnfld.mm"
include "cnrg.mm"
include "wcel.mm"
include "cz.mm"
include "csubrg.mm"
include "cfv.mm"
include "zring.mm"
include "cnnrg.mm"
include "zsubrg.mm"
include "df-zring.mm"
include "subrgnrg.mm"
include "mp2an.mm"

theorem zringnrg



  assert |- ZZring e. NrmRing

  proof
    ccnfld
    cnrg
    wcel
    cz
    ccnfld
    csubrg
    cfv
    wcel
    zring
    cnrg
    wcel
    cnnrg
    zsubrg
    cz
    ccnfld
    zring
    df-zring
    subrgnrg
    mp2an
end
