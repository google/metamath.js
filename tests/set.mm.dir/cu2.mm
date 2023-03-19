include "c2.mm"
include "c3.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "c8.mm"
include "df-3.mm"
include "oveq2i.mm"
include "cmul.mm"
include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "wceq.mm"
include "2cn.mm"
include "2nn0.mm"
include "expp1.mm"
include "mp2an.mm"
include "c4.mm"
include "sq2.mm"
include "oveq1i.mm"
include "4t2e8.mm"
include "eqtri.mm"

theorem cu2



  assert |- ( 2 ^ 3 ) = 8

  proof
    c2
    c3
    cexp
    co
    c2
    c2
    c1
    caddc
    co
    #
    cexp
    co
    #
    c8
    c3
    @0
    c2
    cexp
    df-3
    oveq2i
    @1
    c2
    c2
    cexp
    co
    #
    c2
    cmul
    co
    #
    c8
    c2
    cc
    wcel
    c2
    cn0
    wcel
    @1
    @3
    wceq
    2cn
    2nn0
    c2
    c2
    expp1
    mp2an
    @3
    c4
    c2
    cmul
    co
    c8
    @2
    c4
    c2
    cmul
    sq2
    oveq1i
    4t2e8
    eqtri
    eqtri
    eqtri
end
