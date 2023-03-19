include "c1.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmin.mm"
include "c8.mm"
include "cdiv.mm"
include "cc0.mm"
include "sq1.mm"
include "oveq1i.mm"
include "1m1e0.mm"
include "eqtri.mm"
include "8cn.mm"
include "0re.mm"
include "8pos.mm"
include "gtneii.mm"
include "div0i.mm"

theorem 2lgsoddprmlem3a



  assert |- ( ( ( 1 ^ 2 ) - 1 ) / 8 ) = 0

  proof
    c1
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
    cc0
    c8
    cdiv
    co
    cc0
    @1
    cc0
    c8
    cdiv
    @1
    c1
    c1
    cmin
    co
    cc0
    @0
    c1
    c1
    cmin
    sq1
    oveq1i
    1m1e0
    eqtri
    oveq1i
    c8
    8cn
    cc0
    c8
    0re
    8pos
    gtneii
    div0i
    eqtri
end
