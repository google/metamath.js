include "c1.mm"
include "cneg.mm"
include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "ci.mm"
include "cmul.mm"
include "df-neg.mm"
include "wceq.mm"
include "caddc.mm"
include "ax-i2m1.mm"
include "0cn.mm"
include "ax-1cn.mm"
include "ax-icn.mm"
include "mulcli.mm"
include "subadd2i.mm"
include "mpbir.mm"
include "eqtr2i.mm"

theorem ixi



  assert |- ( _i x. _i ) = -u 1

  proof
    c1
    cneg
    cc0
    c1
    cmin
    co
    #
    ci
    ci
    cmul
    co
    #
    c1
    df-neg
    @0
    @1
    wceq
    @1
    c1
    caddc
    co
    cc0
    wceq
    ax-i2m1
    cc0
    c1
    @1
    0cn
    ax-1cn
    ci
    ci
    ax-icn
    ax-icn
    mulcli
    subadd2i
    mpbir
    eqtr2i
end
