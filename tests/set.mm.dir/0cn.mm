include "ci.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "cc0.mm"
include "cc.mm"
include "ax-i2m1.mm"
include "wcel.mm"
include "ax-icn.mm"
include "mulcl.mm"
include "mp2an.mm"
include "ax-1cn.mm"
include "addcl.mm"
include "eqeltrri.mm"

theorem 0cn



  assert |- 0 e. CC

  proof
    ci
    ci
    cmul
    co
    #
    c1
    caddc
    co
    #
    cc0
    cc
    ax-i2m1
    @0
    cc
    wcel
    #
    c1
    cc
    wcel
    @1
    cc
    wcel
    ci
    cc
    wcel
    #
    @3
    @2
    ax-icn
    ax-icn
    ci
    ci
    mulcl
    mp2an
    ax-1cn
    @0
    c1
    addcl
    mp2an
    eqeltrri
end
