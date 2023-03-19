include "cc0.mm"
include "c1.mm"
include "cmul.mm"
include "co.mm"
include "clt.mm"
include "cr.mm"
include "wcel.mm"
include "wne.mm"
include "wbr.mm"
include "1re.mm"
include "ax-1ne0.mm"
include "msqgt0.mm"
include "mp2an.mm"
include "ax-1cn.mm"
include "mulid1i.mm"
include "breqtri.mm"

theorem 0lt1



  assert |- 0 < 1

  proof
    cc0
    c1
    c1
    cmul
    co
    #
    c1
    clt
    c1
    cr
    wcel
    c1
    cc0
    wne
    cc0
    @0
    clt
    wbr
    1re
    ax-1ne0
    c1
    msqgt0
    mp2an
    c1
    ax-1cn
    mulid1i
    breqtri
end
