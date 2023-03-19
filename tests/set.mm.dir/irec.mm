include "c1.mm"
include "ci.mm"
include "cdiv.mm"
include "co.mm"
include "cneg.mm"
include "wceq.mm"
include "cmul.mm"
include "ax-icn.mm"
include "mulneg2i.mm"
include "ixi.mm"
include "ax-1cn.mm"
include "mulcli.mm"
include "negcon2i.mm"
include "mpbir.mm"
include "eqtr4i.mm"
include "negicn.mm"
include "ine0.mm"
include "divmuli.mm"

theorem irec



  assert |- ( 1 / _i ) = -u _i

  proof
    c1
    ci
    cdiv
    co
    ci
    cneg
    #
    wceq
    ci
    @0
    cmul
    co
    #
    c1
    wceq
    @1
    ci
    ci
    cmul
    co
    #
    cneg
    #
    c1
    ci
    ci
    ax-icn
    ax-icn
    mulneg2i
    c1
    @3
    wceq
    @2
    c1
    cneg
    wceq
    ixi
    c1
    @2
    ax-1cn
    ci
    ci
    ax-icn
    ax-icn
    mulcli
    negcon2i
    mpbir
    eqtr4i
    c1
    ci
    @0
    ax-1cn
    ax-icn
    negicn
    ine0
    divmuli
    mpbir
end
