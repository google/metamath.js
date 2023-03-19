include "ci.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "ax-1ne0.mm"
include "neii.mm"
include "caddc.mm"
include "co.mm"
include "cmul.mm"
include "oveq2.mm"
include "ax-icn.mm"
include "mul01i.mm"
include "syl6req.mm"
include "oveq1d.mm"
include "ax-1cn.mm"
include "addid2i.mm"
include "ax-i2m1.mm"
include "3eqtr3g.mm"
include "mto.mm"
include "neir.mm"

theorem ine0



  assert |- _i =/= 0

  proof
    ci
    cc0
    ci
    cc0
    wceq
    #
    c1
    cc0
    wceq
    c1
    cc0
    ax-1ne0
    neii
    @0
    cc0
    c1
    caddc
    co
    ci
    ci
    cmul
    co
    #
    c1
    caddc
    co
    c1
    cc0
    @0
    cc0
    @1
    c1
    caddc
    @0
    @1
    ci
    cc0
    cmul
    co
    cc0
    ci
    cc0
    ci
    cmul
    oveq2
    ci
    ax-icn
    mul01i
    syl6req
    oveq1d
    c1
    ax-1cn
    addid2i
    ax-i2m1
    3eqtr3g
    mto
    neir
end
