include "c1.mm"
include "cneg.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "neg0.mm"
include "0lt1.mm"
include "eqbrtri.mm"
include "1re.mm"
include "0re.mm"
include "ltnegcon1i.mm"
include "mpbir.mm"

theorem neg1lt0



  assert |- -u 1 < 0

  proof
    c1
    cneg
    cc0
    clt
    wbr
    cc0
    cneg
    #
    c1
    clt
    wbr
    @0
    cc0
    c1
    clt
    neg0
    0lt1
    eqbrtri
    c1
    cc0
    1re
    0re
    ltnegcon1i
    mpbir
end
