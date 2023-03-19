include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "c2.mm"
include "clt.mm"
include "wbr.mm"
include "1div1e1.mm"
include "1lt2.mm"
include "eqbrtri.mm"
include "1re.mm"
include "2re.mm"
include "0lt1.mm"
include "2pos.mm"
include "ltdiv23ii.mm"
include "mpbi.mm"

theorem halflt1



  assert |- ( 1 / 2 ) < 1

  proof
    c1
    c1
    cdiv
    co
    #
    c2
    clt
    wbr
    c1
    c2
    cdiv
    co
    c1
    clt
    wbr
    @0
    c1
    c2
    clt
    1div1e1
    1lt2
    eqbrtri
    c1
    c1
    c2
    1re
    1re
    2re
    0lt1
    2pos
    ltdiv23ii
    mpbi
end
