include "c3.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "c8.mm"
include "cdiv.mm"
include "c9.mm"
include "sq3.mm"
include "oveq1i.mm"
include "8cn.mm"
include "ax-1cn.mm"
include "df-9.mm"
include "mvrraddi.mm"
include "eqtri.mm"
include "cc0.mm"
include "0re.mm"
include "8pos.mm"
include "gtneii.mm"
include "dividi.mm"

theorem 2lgsoddprmlem3b



  assert |- ( ( ( 3 ^ 2 ) - 1 ) / 8 ) = 1

  proof
    c3
    c2
    cexp
    co
    #
    c1
    cmin
    co
    #
    c8
    cdiv
    co
    c8
    c8
    cdiv
    co
    c1
    @1
    c8
    c8
    cdiv
    @1
    c9
    c1
    cmin
    co
    c8
    @0
    c9
    c1
    cmin
    sq3
    oveq1i
    c9
    c8
    c1
    8cn
    ax-1cn
    df-9
    mvrraddi
    eqtri
    oveq1i
    c8
    8cn
    cc0
    c8
    0re
    8pos
    gtneii
    dividi
    eqtri
end
