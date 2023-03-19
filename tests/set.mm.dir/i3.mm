include "ci.mm"
include "c3.mm"
include "cexp.mm"
include "co.mm"
include "c2.mm"
include "c1.mm"
include "caddc.mm"
include "cneg.mm"
include "df-3.mm"
include "oveq2i.mm"
include "cmul.mm"
include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "wceq.mm"
include "ax-icn.mm"
include "2nn0.mm"
include "expp1.mm"
include "mp2an.mm"
include "i2.mm"
include "oveq1i.mm"
include "mulm1i.mm"
include "eqtri.mm"

theorem i3



  assert |- ( _i ^ 3 ) = -u _i

  proof
    ci
    c3
    cexp
    co
    ci
    c2
    c1
    caddc
    co
    #
    cexp
    co
    #
    ci
    cneg
    #
    c3
    @0
    ci
    cexp
    df-3
    oveq2i
    @1
    ci
    c2
    cexp
    co
    #
    ci
    cmul
    co
    #
    @2
    ci
    cc
    wcel
    c2
    cn0
    wcel
    @1
    @4
    wceq
    ax-icn
    2nn0
    ci
    c2
    expp1
    mp2an
    @4
    c1
    cneg
    #
    ci
    cmul
    co
    @2
    @3
    @5
    ci
    cmul
    i2
    oveq1i
    ci
    ax-icn
    mulm1i
    eqtri
    eqtri
    eqtri
end
